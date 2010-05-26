/*
 * Copyright (C) 2007 The Android Open Source Project
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

#include <ctype.h>
#include <errno.h>
#include <fcntl.h>
#include <getopt.h>
#include <limits.h>
#include <linux/input.h>
#include <stdio.h>
#include <dirent.h>
#include <stdlib.h>
#include <string.h>
#include <sys/reboot.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <time.h>
#include <unistd.h>
#include <termios.h>

#include "bootloader.h"
#include "commands.h"
#include "common.h"
#include "cutils/properties.h"
#include "firmware.h"
#include "install.h"
#include "minui/minui.h"
#include "minzip/DirUtil.h"
#include "roots.h"

static const struct option OPTIONS[] = {
  { "send_intent", required_argument, NULL, 's' },
  { "update_package", required_argument, NULL, 'u' },
  { "wipe_data", no_argument, NULL, 'w' },
  { "wipe_cache", no_argument, NULL, 'c' },
};

static const char *COMMAND_FILE = "CACHE:recovery/command";
static const char *INTENT_FILE = "CACHE:recovery/intent";
static const char *LOG_FILE = "CACHE:recovery/log";
static const char *SDCARD_PATH = "SDCARD:";
#define SDCARD_PATH_LENGTH 7
static const char *TEMPORARY_LOG_FILE = "/tmp/recovery.log";

static char file_queue[PATH_MAX];
static int paste_flag = 0;
static int deletion = 0;

/*
 * The recovery tool communicates with the main system through /cache files.
 *   /cache/recovery/command - INPUT - command line for tool, one arg per line
 *   /cache/recovery/log - OUTPUT - combined log file from recovery run(s)
 *   /cache/recovery/intent - OUTPUT - intent that was passed in
 *
 * The arguments which may be supplied in the recovery.command file:
 *   --send_intent=anystring - write the text out to recovery.intent
 *   --update_package=root:path - verify install an OTA package file
 *   --wipe_data - erase user data (and cache), then reboot
 *   --wipe_cache - wipe cache (but not user data), then reboot
 *
 * After completing, we remove /cache/recovery/command and reboot.
 * Arguments may also be supplied in the bootloader control block (BCB).
 * These important scenarios must be safely restartable at any point:
 *
 * FACTORY RESET
 * 1. user selects "factory reset"
 * 2. main system writes "--wipe_data" to /cache/recovery/command
 * 3. main system reboots into recovery
 * 4. get_args() writes BCB with "boot-recovery" and "--wipe_data"
 *    -- after this, rebooting will restart the erase --
 * 5. erase_root() reformats /data
 * 6. erase_root() reformats /cache
 * 7. finish_recovery() erases BCB
 *    -- after this, rebooting will restart the main system --
 * 8. main() calls reboot() to boot main system
 *
 * OTA INSTALL
 * 1. main system downloads OTA package to /cache/some-filename.zip
 * 2. main system writes "--update_package=CACHE:some-filename.zip"
 * 3. main system reboots into recovery
 * 4. get_args() writes BCB with "boot-recovery" and "--update_package=..."
 *    -- after this, rebooting will attempt to reinstall the update --
 * 5. install_package() attempts to install the update
 *    NOTE: the package install must itself be restartable from any point
 * 6. finish_recovery() erases BCB
 *    -- after this, rebooting will (try to) restart the main system --
 * 7. ** if install failed **
 *    7a. prompt_and_wait() shows an error icon and waits for the user
 *    7b; the user reboots (pulling the battery, etc) into the main system
 * 8. main() calls maybe_install_firmware_update()
 *    ** if the update contained radio/hboot firmware **:
 *    8a. m_i_f_u() writes BCB with "boot-recovery" and "--wipe_cache"
 *        -- after this, rebooting will reformat cache & restart main system --
 *    8b. m_i_f_u() writes firmware image into raw cache partition
 *    8c. m_i_f_u() writes BCB with "update-radio/hboot" and "--wipe_cache"
 *        -- after this, rebooting will attempt to reinstall firmware --
 *    8d. bootloader tries to flash firmware
 *    8e. bootloader writes BCB with "boot-recovery" (keeping "--wipe_cache")
 *        -- after this, rebooting will reformat cache & restart main system --
 *    8f. erase_root() reformats /cache
 *    8g. finish_recovery() erases BCB
 *        -- after this, rebooting will (try to) restart the main system --
 * 9. main() calls reboot() to boot main system
 */

static const int MAX_ARG_LENGTH = 4096;
static const int MAX_ARGS = 100;

static int do_reboot = 1;
static int usb_ms = 0;

// open a file given in root:path format, mounting partitions as necessary
static FILE*
fopen_root_path(const char *root_path, const char *mode) {
    if (ensure_root_path_mounted(root_path) != 0) {
        LOGE("Can't mount %s\n", root_path);
        return NULL;
    }

    char path[PATH_MAX] = "";
    if (translate_root_path(root_path, path, sizeof(path)) == NULL) {
        LOGE("Bad path %s\n", root_path);
        return NULL;
    }

    // When writing, try to create the containing directory, if necessary.
    // Use generous permissions, the system (init.rc) will reset them.
    if (strchr("wa", mode[0])) dirCreateHierarchy(path, 0777, NULL, 1);

    FILE *fp = fopen(path, mode);
    return fp;
}

// close a file, log an error if the error indicator is set
static void
check_and_fclose(FILE *fp, const char *name) {
    fflush(fp);
    if (ferror(fp)) LOGE("Error in %s\n(%s)\n", name, strerror(errno));
    fclose(fp);
}

// command line args come from, in decreasing precedence:
//   - the actual command line
//   - the bootloader control block (one per line, after "recovery")
//   - the contents of COMMAND_FILE (one per line)
static void
get_args(int *argc, char ***argv) {
    struct bootloader_message boot;
    memset(&boot, 0, sizeof(boot));
    get_bootloader_message(&boot);  // this may fail, leaving a zeroed structure

    if (boot.command[0] != 0 && boot.command[0] != 255) {
        LOGI("Boot command: %.*s\n", sizeof(boot.command), boot.command);
    }

    if (boot.status[0] != 0 && boot.status[0] != 255) {
        LOGI("Boot status: %.*s\n", sizeof(boot.status), boot.status);
    }

    // --- if arguments weren't supplied, look in the bootloader control block
    if (*argc <= 1) {
        boot.recovery[sizeof(boot.recovery) - 1] = '\0';  // Ensure termination
        const char *arg = strtok(boot.recovery, "\n");
        if (arg != NULL && !strcmp(arg, "recovery")) {
            *argv = (char **) malloc(sizeof(char *) * MAX_ARGS);
            (*argv)[0] = strdup(arg);
            for (*argc = 1; *argc < MAX_ARGS; ++*argc) {
                if ((arg = strtok(NULL, "\n")) == NULL) break;
                (*argv)[*argc] = strdup(arg);
            }
            LOGI("Got arguments from boot message\n");
        } else if (boot.recovery[0] != 0 && boot.recovery[0] != 255) {
            LOGE("Bad boot message\n\"%.20s\"\n", boot.recovery);
        }
    }

    // --- if that doesn't work, try the command file
    if (*argc <= 1) {
        FILE *fp = fopen_root_path(COMMAND_FILE, "r");
        if (fp != NULL) {
            char *argv0 = (*argv)[0];
            *argv = (char **) malloc(sizeof(char *) * MAX_ARGS);
            (*argv)[0] = argv0;  // use the same program name

            char buf[MAX_ARG_LENGTH];
            for (*argc = 1; *argc < MAX_ARGS; ++*argc) {
                if (!fgets(buf, sizeof(buf), fp)) break;
                (*argv)[*argc] = strdup(strtok(buf, "\r\n"));  // Strip newline.
            }

            check_and_fclose(fp, COMMAND_FILE);
            LOGI("Got arguments from %s\n", COMMAND_FILE);
        }
    }

    // --> write the arguments we have back into the bootloader control block
    // always boot into recovery after this (until finish_recovery() is called)
    strlcpy(boot.command, "boot-recovery", sizeof(boot.command));
    strlcpy(boot.recovery, "recovery\n", sizeof(boot.recovery));
    int i;
    for (i = 1; i < *argc; ++i) {
        strlcat(boot.recovery, (*argv)[i], sizeof(boot.recovery));
        strlcat(boot.recovery, "\n", sizeof(boot.recovery));
    }
    set_bootloader_message(&boot);
}


// clear the recovery command and prepare to boot a (hopefully working) system,
// copy our log file to cache as well (for the system to read), and
// record any intent we were asked to communicate back to the system.
// this function is idempotent: call it as many times as you like.
static void
finish_recovery(const char *send_intent)
{
    // By this point, we're ready to return to the main system...
    if (send_intent != NULL) {
        FILE *fp = fopen_root_path(INTENT_FILE, "w");
        if (fp == NULL) {
            LOGE("Can't open %s\n", INTENT_FILE);
        } else {
            fputs(send_intent, fp);
            check_and_fclose(fp, INTENT_FILE);
        }
    }

    // Copy logs to cache so the system can find out what happened.
    FILE *log = fopen_root_path(LOG_FILE, "a");
    if (log == NULL) {
        LOGE("Can't open %s\n", LOG_FILE);
    } else {
        FILE *tmplog = fopen(TEMPORARY_LOG_FILE, "r");
        if (tmplog == NULL) {
            LOGE("Can't open %s\n", TEMPORARY_LOG_FILE);
        } else {
            static long tmplog_offset = 0;
            fseek(tmplog, tmplog_offset, SEEK_SET);  // Since last write
            char buf[4096];
            while (fgets(buf, sizeof(buf), tmplog)) fputs(buf, log);
            tmplog_offset = ftell(tmplog);
            check_and_fclose(tmplog, TEMPORARY_LOG_FILE);
        }
        check_and_fclose(log, LOG_FILE);
    }

    // Reset the bootloader message to revert to a normal main system boot.
    struct bootloader_message boot;
    memset(&boot, 0, sizeof(boot));
    set_bootloader_message(&boot);

    // Remove the command file, so recovery won't repeat indefinitely.
    char path[PATH_MAX] = "";
    if (ensure_root_path_mounted(COMMAND_FILE) != 0 ||
        translate_root_path(COMMAND_FILE, path, sizeof(path)) == NULL ||
        (unlink(path) && errno != ENOENT)) {
        LOGW("Can't unlink %s\n", COMMAND_FILE);
    }

    sync();  // For good measure.
}

#define TEST_AMEND 0
#if TEST_AMEND
static void
test_amend()
{
    extern int test_symtab(void);
    extern int test_cmd_fn(void);
    int ret;
    LOGD("Testing symtab...\n");
    ret = test_symtab();
    LOGD("  returned %d\n", ret);
    LOGD("Testing cmd_fn...\n");
    ret = test_cmd_fn();
    LOGD("  returned %d\n", ret);
}
#endif  // TEST_AMEND

static int
erase_root(const char *root)
{
    ui_set_background(BACKGROUND_ICON_INSTALLING);
    ui_show_indeterminate_progress();
    ui_print("Formatting %s..", root);
    return format_root_device(root);
}

int
get_menu_selection(char** headers, char** items) {
    ui_clear_key_queue();
    ui_start_menu(headers, items);
    int selected = 0;
    int chosen_item = -1;

    while (chosen_item < 0) {
        int key = ui_text_visible() ? ui_wait_key() : 0;

        switch (key) {
	        case KEY_UP:
		case KEY_DREAM_VOLUMEUP:
	                --selected;
	                selected = ui_menu_select(selected);
	                break;
	        case KEY_DOWN:
		case KEY_DREAM_VOLUMEDOWN:
	                ++selected;
	                selected = ui_menu_select(selected);
	                break;
		case KEY_DREAM_MENU:
			deletion = 1;
	        case KEY_I5700_CENTER:
	                chosen_item = selected + ui_menu_offset();
	                break;
	        case KEY_DREAM_BACK:
	                chosen_item = KEY_DREAM_BACK;
	                break;
        }
    }
    ui_clear_key_queue();
    return chosen_item;
}

char* choose_file_menu(const char* directory, const char* prefix, const char* extension, const char* headers[])
{
    char path[PATH_MAX] = "";
    DIR *dir;
    struct dirent *de;
    int total = 0, dirs = 0, other = 0;
    int i, j;
    char** files;
    char** list;
    char** dirlist;
    char** otherlist;

    dir = opendir(directory);
    if (dir == NULL) {
        ui_print("Couldn't open directory.\n");
        return NULL;
    }
  
    const int extension_length = strlen(extension);
  
    while ((de=readdir(dir)) != NULL) {
        if (de->d_name[0] != '.' && strlen(de->d_name) > extension_length && starts_with(de->d_name, prefix) && ends_with(de->d_name, extension)) {
            if (de->d_type == DT_DIR && !extension_length) {
		dirs++;
	    } else if (de->d_type != DT_DIR) {
		other++;
	    }
        }
    }
    
    total = dirs+other;

    if (total) {
	files = (char**) malloc((total+1)*sizeof(*files));
	files[total]=NULL;

	list = (char**) malloc((total+1)*sizeof(*list));
	list[total]=NULL;

	dirlist = (char**) malloc((dirs+1)*sizeof(*dirlist));
	dirlist[dirs]=NULL;

	otherlist = (char**) malloc((other+1)*sizeof(*otherlist));
	otherlist[other]=NULL;

	rewinddir(dir);

	i = j = 0;
	while ((de = readdir(dir)) != NULL) {
		if (de->d_name[0] != '.' && strlen(de->d_name) > extension_length && starts_with(de->d_name, prefix) && ends_with(de->d_name, extension)) {
		    if (de->d_type == DT_DIR && !extension_length) {
			dirlist[i] = (char*) malloc(strlen(de->d_name)+2);
			strcpy(dirlist[i], de->d_name);
			strcat(dirlist[i], "/");
			i++;
		    } else if (de->d_type != DT_DIR) {
			otherlist[j] = (char*) malloc(strlen(de->d_name)+1);
			strcpy(otherlist[j], de->d_name);
			j++;
		    }
		}
	}

	sorted(dirlist, dirs);
	sorted(otherlist, other);

	int k;
	for (k = 0; k < dirs; k++) {
		files[k] = (char*) malloc(strlen(directory)+strlen(dirlist[k])+1);
		strcpy(files[k], directory);
		strcat(files[k], dirlist[k]);

		list[k] = (char*) malloc(strlen(dirlist[k])+1);
		strcpy(list[k], dirlist[k]);
	}

	for (; k < total; k++) {
		files[k] = (char*) malloc(strlen(directory)+strlen(otherlist[k-dirs])+1);
		strcpy(files[k], directory);
		strcat(files[k], otherlist[k-dirs]);

		list[k] = (char*) malloc(strlen(otherlist[k-dirs])+1);
		strcpy(list[k], otherlist[k-dirs]);
	}
    } else {
	files = (char**) malloc(2*sizeof(*files));
	files[1]=NULL;

	list = (char**) malloc(2*sizeof(*list));
	list[1]=NULL;

	files[0] = (char*) malloc(strlen(directory)+strlen("")+1);
	list[0] = (char*) malloc(strlen("")+1);
	strcpy(files[0], directory);
	strcat(files[0], "");
	strcpy(list[0], "");
    }

    if (closedir(dir) <0) {
	LOGE("Failure closing directory.");
	return NULL;
    }

    for (;;)
    {
	finish_recovery(NULL);
	ui_reset_progress();
        int chosen_item = get_menu_selection(headers, list);
        if (chosen_item == KEY_DREAM_BACK)
            break;
        return files[chosen_item];
    }
    return NULL;
}

int
confirm_key(char string[])
{
	ui_print("\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n");
	ui_print("\n\n- This will %s!", string);
	ui_print("\n- Press HOME to confirm or");
	ui_print("\n- any other key to abort...");
	
	return ui_wait_key() == KEY_DREAM_HOME;
}

char*
strn (char* string, size_t n)
{
	if (!n) return NULL;
	return strndup(string, n);
}

char*
strnr(char* string, size_t n)
{
	if (!n)	return NULL;
	return strndup(string + n, strlen(string));
}

int
ends_with(char* string, char* key)
{
	if (!strlen(key)) return 1;
	if (strlen(key) > strlen(string)) return 0;
	return !strcmp(strnr(string, strlen(string)-strlen(key)), key);
}

int starts_with(char* string, char* key)
{
	if (!strlen(key)) return 1;
	if (strlen(key) > strlen(string)) return 0;
	return !strcmp(strn(string, strlen(key)), key);
}

static void
backup(int option)
{
	static char* partition[] = {"/system", "/data", "/system and /data", NULL};
	static char* file[] = {"system", "data", "full", NULL};

	char message[strlen(partition[option])+9];
	sprintf(message, "back up %s", partition[option]);
	char location[strlen(file[option])+20];
	sprintf(location, "/sdcard/sdx/backup/%s", file[option]);

	if (confirm_key(message)) {
        	int error = 0;
        	pid_t pid = fork();
        	if (pid == 0) {
			time_t rawtime;
			struct tm * timeinfo;
			char formattime[16];
			time ( &rawtime );
			timeinfo = localtime ( &rawtime );
			strftime (formattime,16,"%m%d%Y%H%M%S",timeinfo);

			char filename[strlen(location)+strlen(formattime)+7];
			sprintf(filename, "%s_%s.tar", location, formattime);

			if (option < 2) {
				error = execl("/sbin/busybox", "tar", "-c", "--exclude=$RFS_LOG.LO$", "-f", filename, partition[option], NULL);
			} else {
				error = execl("/sbin/busybox", "tar", "-c", "--exclude=$RFS_LOG.LO$", "-f", filename, "/system", "/data", NULL);
			}
                	_exit(-1);
        	}

		int status;
        	while (waitpid(pid, &status, WNOHANG) == 0) {
                	ui_print(".");
                	sleep(1);
        	}

        	if (error != 0){
                	ui_print("\n\nError backing up %s", partition[option]);
        	} else {
                	ui_print("\n\n%s backed up successfully!", partition[option]); 
        	}
	} else {
                ui_print("\n\nBackup aborted.\n");
        }
}

static void
restore(char* file, char* partition)
{
	if (!file) {
		return;
	}

	if (deletion) {
		if(confirm_key("delete this file")) {
			if (remove(file)) {
				ui_print("\nUnable to delete the file");
			} else {
				ui_print("\nFile deleted successfully");
			}
		} else {
			ui_print("\nDelete aborted");
		}
		deletion = 0;
		return;		
	}

	char message[strlen(partition)+9];
	sprintf(message, "restore %s", partition);
	
	if (confirm_key(message)) {
        	int error = 0;
        	pid_t pid = fork();
        	if (pid == 0) {
                	error = execl("/sbin/busybox", "tar", "-x", "-f", file, NULL);
                	_exit(-1);
        	}

		int status;
        	while (waitpid(pid, &status, WNOHANG) == 0) {
                	ui_print(".");
                	sleep(1);
        	}

        	if (error != 0){
                	ui_print("\n\nError restoring %s", partition);
        	} else {
                	ui_print("\n\n%s restored successfully!", partition); 
        	}
	} else {
                ui_print("\n\nRestore aborted.\n");
        }
}

static void
flash(char* file, char* partition)
{
	FILE *fp = fopen(file, "r");
	if (!fp) {
		ui_print("\nFile not found. Flash canceled");
		return 1;
	} else {
		fclose(fp);
	}

	char message[strlen(partition)+21];
	sprintf(message, "flash the %s partition", partition);

	if (confirm_key(message)) {
        	int error = 0;
        	pid_t pid = fork();
        	if (pid == 0) {
                	error = execl("/sbin/flash_image", "flash_image", partition, file, NULL);
                	_exit(-1);
        	}

		ui_print("\n\nFlashing %s.", partition);
		int status;
        	while (waitpid(pid, &status, WNOHANG) == 0) {
                	ui_print(".");
                	sleep(1);
        	}

        	if (error != 0){
                	ui_print("\n\nError flashing %s", partition);
        	} else {
                	ui_print("\n\n%s flashed successfully!", partition); 
        	}
	} else {
                ui_print("\n\nFlash aborted");
        }
}

static void
partition_options()
{
    static char* headers[] = {		"      Backup, Restore, Flash",
                        		"",
                        		"Use Up/Down and OK to select",
                        		"Back returns to main menu",
                        		"",
                        		NULL };

#define BACKUP_SYSTEM		0
#define BACKUP_DATA		1
#define BACKUP_ALL		2
#define RESTORE_SYSTEM		4
#define RESTORE_DATA		5
#define RESTORE_ALL		6
#define FLASH_KERNEL		8
#define FLASH_LOGO		9
#define FLASH_RECOVERY		10

    static char* items[] = { 	"Backup /system",
				"Backup /data",
				"Backup both (/system and /data)",
				"---------------------------------",
				"Restore /system",
				"Restore /data",
				"Restore both (/system and /data)",
				"---------------------------------",
				"Flash Kernel (zImage)",
			     	"Flash Boot Screen (logo.png)",
			     	"Flash Recovery (recovery.rfs)",
			 	NULL };

    int chosen_item;     
    ensure_root_path_mounted("SDCARD:");

    while (chosen_item != KEY_DREAM_BACK) {
	chosen_item = get_menu_selection(headers, items);   

	switch (chosen_item) {
		case BACKUP_SYSTEM:
		case BACKUP_DATA:
		case BACKUP_ALL:
			backup(chosen_item);
			break;

		case RESTORE_SYSTEM:
			restore(choose_file_menu("/sdcard/sdx/backup/", "system", ".tar", headers), "/system");
			break;

		case RESTORE_DATA:
			restore(choose_file_menu("/sdcard/sdx/backup/", "data", ".tar", headers), "/data");
			break;

		case RESTORE_ALL:
			restore(choose_file_menu("/sdcard/sdx/backup/", "full", ".tar", headers), "/system and /data");
			break;

		case FLASH_KERNEL: 
			flash("/sdcard/sdx/updates/zImage", "boot");
			break;

		case FLASH_LOGO:
			flash("/sdcard/sdx/updates/logo.png", "boot3");
			break;

		case FLASH_RECOVERY:
			flash("/sdcard/sdx/updates/recovery.rfs", "recovery");
			break;

		default:
			break;
	}
    }
}

static int
reboot_options()
{
    static char* headers[] = { 		"          Reboot Options",
                        		"",
                        		"Use Up/Down and OK to select",
                        		"Back returns to main menu",
                        		"",
                        		NULL };

#define REBOOT		0
#define REBOOT_RECOVERY		1
#define REBOOT_POWEROFF		2

    static char* items[] = { 	"Reboot to System",
			     				"Reboot to Recovery",
			     				"Power Off Phone",
			 			     	NULL };

    int chosen_item = get_menu_selection(headers, items);
            switch (chosen_item) {

		case REBOOT:
			return 1;
				
		case REBOOT_RECOVERY:
			system("/sbin/reboot recovery");

		case REBOOT_POWEROFF:
			return 2;

		case KEY_DREAM_BACK:
			return 0;
		}		
}

// string sorter I found!

int
compare_elements(const void *a, const void *b)
{
    const char **ia = (const char **)a;
    const char **ib = (const char **)b;
    return strcmp(*ia, *ib);
}

void
sorted (char **array, int size)
{
  qsort (array, size, sizeof (char *), compare_elements);
}

// end of magical string sorter!

static void
browse_files()
{
    char* headers[] = { "          Browse files", "", "Use Up/Down and OK to select", "Back returns to top directory", "", NULL};
    char path[PATH_MAX] = "/";
    char* file;
    char* pch;

    for(;;) {
	finish_recovery(NULL);
	ui_reset_progress();

	file = choose_file_menu(path, "", "", headers);

	if (!file) {
		if (strlen(path) == 1) {
			break;
		}
		strcpy(path, strndup(path, strlen(path)-1));
		pch = strrchr(path, '/');
		strcpy(path, strndup(path, pch-path+1));

	} else if (strcmp(file + strlen(file) - strlen("/"), "/") == 0 && !deletion) {
		strcpy(path, file);
	} else {
		file_options(path, strnr(file, strlen(path)));
		deletion = 0;
	}
    }
}

char*
file_option_text(char file[])
{
	static char* string[] = {"Apply zip", "Restore system backup", "Restore data backup",
				 "Restore full backup", "Flash recovery kernel", "Flash boot logo",
				 "Flash kernel image", "No associated action", NULL};
	if (ends_with(file, "/")) {
		return string[7];
	}

	if (ends_with(file, ".zip")) {
		return string[0];
	} else if (ends_with(file, ".tar")) {
		if (starts_with(file, "system")) {
			return string[1];
		} else if (starts_with(file, "data")) {
			return string[2];
		} else if (starts_with(file, "full")) {
			return string[3];
		} else {
			return string[7];
		}
	} else if (ends_with(file, ".rfs")) {
		return string[4];
	} else if (ends_with(file, ".png")) {
		return string[5];
	} else if (ends_with(file, "zImage") && strlen(file) == 6) {
		return string[6];
	} else {
		return string[7];
	}
}

void
file_option_action(char* path, char* file)
{
	char* name[strlen(path)+strlen(file)+1];
	sprintf(name, "%s%s", path, file);
	
	if (ends_with(file, ".zip")) {
		if (confirm_key("apply a zip file")) {
			if (install_package(name)) {
				ui_print("\nError installing package!");
			} else {
				ui_print("\nPackage installed successfully!");
			}
		}			
	} else if (ends_with(file, ".tar")) {
		if (starts_with(file, "system")) {
			restore(name, "/system");
		} else if (starts_with(file, "data")) {
			restore(name, "/data");
		} else if (starts_with(file, "full")) {
			restore(name, "/system and /data");
		}
	} else if (ends_with(file, ".rfs")) {
		flash(name, "recovery");
	} else if (ends_with(file, ".png")) {
		flash(name, "boot3");
	} else if (ends_with(file, "zImage") && strlen(file) == 6) {
		flash(name, "boot");
	}
}

void
file_options(char* path, char* file)
{
     static char* headers[] = { 	"Choose an option",
    					"",
    					"Use Up/Down and OK to select",
                        		"Back returns to the selected file",
    					"",
                        		NULL }; 

#define ITEM_SPECIFIC		0
#define ITEM_CUT		1
#define ITEM_COPY		2
#define ITEM_PASTE		3
#define ITEM_DELETE       	4

    char* items[] = {			file_option_text(file),
					"Cut",
					"Copy",
					"Paste",
					"Delete",
					NULL };

    int chosen_item = get_menu_selection(headers, items);
    deletion = 0;

    if (chosen_item != KEY_DREAM_BACK) {
	    char *cutcopy[] = {"move", "copy", NULL};
	    char move[strlen(path) + strlen(file_queue) + 5];
	    char act[5];
            switch (chosen_item) {
                case ITEM_SPECIFIC:
		    file_option_action(path, file);
                    break;

                case ITEM_CUT:
		case ITEM_COPY:
		    strcpy(file_queue, path);
		    strcat(file_queue, file);
		    paste_flag = chosen_item;
		    ui_print("\nMarked to %s. Press MENU and\nselect Paste in the desired\nlocation to %s"\
				, cutcopy[chosen_item-1], cutcopy[chosen_item-1]);
                    break;
                	
                case ITEM_PASTE:
		    if (!paste_flag) {
			ui_print("\nNothing to paste.");
			break;
		    }
		    switch (paste_flag) {
			case 1:
				sprintf(move, "mv \"%s\" \"%s\"", file_queue, path);
				strcpy(act, "move");
			case 2:
				sprintf(move, "cp \"%s\" \"%s\"", file_queue, path);
				strcpy(act, "copy");
		    }

		    if (!system(move)) {
			ui_print("\nFile %s successful!", act);
		    } else {
			ui_print("\nUnable to %s the file!", act);
		    }
		    paste_flag = 0;
		    break;
                	
                case ITEM_DELETE:
		    ui_print("\nPress MENU to confirm delete!");
		    int key = ui_wait_key();
		    if (key == KEY_DREAM_MENU) {
			char *remove = (char*) malloc(strlen(path)+strlen(file)+strlen("rm -r")+1);
			sprintf(remove, "rm -r %s%s", path, file);
			int error = system(remove);
			if (!error) {
				ui_print("\nFile deleted successfully!");
			} else {
				ui_print("\nUnable to delete the file!");
			}
		    } else {
			ui_print("\nDelete aborted!");
		    }
                    break;
            }
    } 
} 

static void
choose_update_file()
{
    if (ensure_root_path_mounted("SDCARD:")) {
	LOGE("Can't mount SDCARD\n");
	return;
    }

    static char* headers[] = { 		"	    Choose update ZIP file",
    					"",
    					"Use Up/Down and OK to select",
                        		"Back returns to main menu",
    					"",
                        		NULL };

    char* file = choose_file_menu("/sdcard/sdx/zip/", "", ".zip", headers);

    if (file && !ends_with(file, "/")) {
	if (deletion) {
		if (confirm_key("delete this file")) {
			if (remove(file) != 0) {
				ui_print("\nCould not delete the file");
			} else {
				ui_print("\nFile successfully deleted!");
			}
		} else {
			ui_print("\nDelete aborted");
		}
		deletion = 0;
	} else {
		if (confirm_key("apply this update")) {
			if (install_package(file) != INSTALL_SUCCESS) {
				ui_print("\nError applying update!");
			} else {
				ui_print("\nUpdate installed! Reboot required");
			}
		} else {
			ui_print("\nUpdate aborted");
		}
	}
   }
}

static void
mount_options()
{
#define SYSTEM	0
#define DATA	1
#define CACHE	2
#define SDCARD	3
#define	SDEXT	4
#define BLANK	5
#define USBMS	6

	static char* headers[] = {	"	      Mount Options",
					"",
					"Use Up/Down and OK to select",
					"Back returns to the main menu",
					"", NULL };
	int chosen_item, i = 0;
	char** items;

	static char* partition[] = { "SYSTEM:", "DATA:", "CACHE:", "SDCARD:", "SDEXT:", NULL };

	while (chosen_item != KEY_DREAM_BACK) {
		items = (char**) malloc(8 * sizeof(char*));

		items[0] = !is_root_path_mounted("SYSTEM:") ? "Mount /system" : "Unmount /system";
		items[1] = !is_root_path_mounted("DATA:") ? "Mount /data" : "Unmount /data";
		items[2] = !is_root_path_mounted("CACHE:") ? "Mount /cache" : "Unmount /cache";
		items[3] = !is_root_path_mounted("SDCARD:") ? "Mount /sdcard" : "Unmount /sdcard";
		items[4] = !is_root_path_mounted("SDEXT:") ? "Mount /sdext" : "Unmount /sdext";
		items[5] = "";
		items[6] = !usb_ms ? "Enable USB Mass Storage" : "Disable USB Mass Storage";
		items[7] = NULL;

		chosen_item = get_menu_selection(headers, items);
		deletion = 0;

		switch (chosen_item) {
			case SYSTEM:
			case DATA:
			case CACHE:
			case SDCARD:
			case SDEXT:
				if (is_root_path_mounted(partition[chosen_item])) {
					ensure_root_path_unmounted(partition[chosen_item]);
				} else {
					if (!ensure_root_path_mounted(partition[chosen_item])) {
						ui_print("\nMounted %s", partition[chosen_item]);
					}
				}
				break;


			case USBMS:
				if (usb_ms) {
					system("echo > /sys/devices/platform/s3c6410-usbgadget/gadget/lun0/file");
				} else {
					system("echo /dev/block/mmcblk0p1 > /sys/devices/platform/s3c6410-usbgadget/gadget/lun0/file");
				}
				usb_ms = !usb_ms;
				break;

			case BLANK:
				continue;

			default:
				break;
		}
	}
}

static void
make_part(int option)
{
	if (!confirm_key("partition your SD card")) {
		ui_print("\nPartition aborted");
		return;
	}

	ui_print("\n\nPartitioning SD card...\n     This will take a while!");

	if (option > 3) {
		if (option > 6) {
			option--;
		}
		option--;
	}

	if (option < 3) setenv("SWAP_SIZE", "96", 1);
	else if (option < 6) setenv("SWAP_SIZE", "96", 1);
	else setenv("SWAP_SIZE", "96", 1);

	if (option == 9) setenv("EXT_SIZE", "0", 1);
	else if (option % 3 == 0) setenv("EXT_SIZE", "128", 1);
	else if (option % 3 == 1) setenv("EXT_SIZE", "256", 1);
	else if (option % 3 == 2) setenv("EXT_SIZE", "512", 1);

	if (option == 9) setenv("ETYPE", "ext2", 1);
	else setenv("ETYPE", "ext3", 1);

	char *command = (char*) malloc(strlen("sdparted -x -s") + 1);
	sprintf(command, "sdparted -x -s");

	if (system(command)) {
		ui_print("\nError partitioning!");
		return;
	}

	ui_print("\nPartition successful!");
}
	

static void
sd_part_options()
{
	ui_end_menu();

	ui_print("\n\n-  CAUTION! Partitioning your SD\n-\
		card will destroy all data\n-\
		stored in it! Only you are\n-\
		responsible for backing it\n-\
		up! Press HOME if you still\n-\
		want to proceed..");

	if (ui_wait_key() != KEY_DREAM_HOME) {
		ui_print("\nPartitioning aborted");
		return;
	}
	ui_clear_key_queue();

	static char* headers[] = {	"	   Partition Options",
					"",
					"Use Up/Down and OK to select",
					"Back returns to the main menu",
					"", NULL };

#define SDPARTED_1 	0
#define SDPARTED_2	1
#define SDPARTED_3	2
#define BLANK_1		3
#define SDPARTED_4	4
#define SDPARTED_5	5
#define SDPARTED_6	6
#define BLANK_2		7
#define SDPARTED_7	8
#define SDPARTED_8	9
#define SDPARTED_9	10
#define BLANK_3		11
#define UNPART		12


	static char* items[] = {	"128mb ext3, 96mb swap, rest FAT",
					"256mb ext3, 96mb swap, rest FAT",
					"512mb ext3, 96mb swap, rest FAT",
					"-------------------------------",
					"128mb ext3, 32mb swap, rest FAT",
					"256mb ext3, 32mb swap, rest FAT",
					"512mb ext3, 32mb swap, rest FAT",
					"-------------------------------",
					"128mb ext3, no swap, rest FAT",
					"256mb ext3, no swap, rest FAT",
					"512mb ext3, no swap, rest FAT",
					"-------------------------------",
					"Format to default (all FAT)",
					NULL };

	for (;;) {
		int chosen_item = get_menu_selection(headers, items);
	
		switch (chosen_item) {
			case BLANK_1:
			case BLANK_2:
			case BLANK_3:
				continue;

			case KEY_DREAM_BACK:
				return;

			default:
				make_part(chosen_item);
				break;
		}
	}
	deletion = 0;
}

static void
advanced_menu()
{
	static char* headers[] = {	"	   Advanced Options",
					"",
					"Use Up/Down and OK to select",
					"Back returns to the main menu",
					"", NULL };

#define CLEAR_DALVIK 	0
#define WIPE_DATA	1
#define APPS_SD		2
#define APPS_CACHE	3
#define APPS_DATA	4

	static char* items[] = {	"Clear Dalvik Cache",
					"Wipe / Factory Reset",
					"Apps2SD",
					"Apps2Cache",
					"Apps2Data (default)",
					NULL };

	for(;;) {
		finish_recovery(NULL);
		ui_reset_progress();

		int chosen_item = get_menu_selection(headers, items);

		switch (chosen_item) {
			case CLEAR_DALVIK:
				if (confirm_key("clear Dalvik Cache")) {
					if (ensure_root_path_mounted("DATA:") == 0) {
						ui_print("\nClearing Dalvik Cache...");
						if (!system("/sbin/busybox rm /data/dalvik-cache/*")) {
							ui_print("\n\nCleared Dalvik Cache!");
						} else {
							ui_print("\n\nCan't clear Dalvik Cache");
						}
					}
				} else {
					ui_print("\nDelete aborted");
				}						
				break;

			case WIPE_DATA:
				if (confirm_key("wipe your data")) {
					if (ensure_root_path_mounted("DATA:") == 0) {	
						ui_print("\nWiping data...");
						erase_root("DATA:");
						erase_root("CACHE:");
						ui_print("\n\nData wipe complete");
					}
				} else {
					ui_print("\nData wipe aborted");
				}	
				break;

			case APPS_SD:
				if (!system("readlink /data/app | grep sd")) {
					ui_print("\nApps already moved to SD");
				} else {
					if (!system("readlink /data/app | grep cache")) {
						ui_print("\n- Apps are currently in\n- /cache/app");
					} else {
						ui_print("\n- Apps are currently in\n- /data/app");
					}

					if (confirm_key("move your apps\nto a partitioned SD card")) {
						if (ensure_root_path_mounted("DATA:") == 0 && ensure_root_path_mounted("SDEXT:") == 0) {
							!system("appsto sd") ? ui_print("\nApps successfully moved!") \
									    : ui_print("\nError moving apps");
						} else {
							ui_print("\nCan't mount /data or /sdcard");
						}
					} else {
						ui_print("\nApps2SD move aborted");
					}
				}
				break;

			case APPS_CACHE:
				if (!system("readlink /data/app | grep cache")) {
					ui_print("\nApps already moved to cache");
				} else {
					if (!system("readlink /data/app | grep sd")) {
						ui_print("\n- Apps are currently in\n- SD card (ext partition)");
					} else {
						ui_print("\n- Apps are currently in\n- /data/app");
					}

					if (confirm_key("move your apps\nto the /cache partition")) {
						if (ensure_root_path_mounted("CACHE:") == 0) {
							!system("appsto cache") ? ui_print("\nApps successfully moved!") \
									    : ui_print("\nError moving apps");
						} else {
							ui_print("\nCan't mount /cache");
						}
					} else {
						ui_print("\nApps2SD move aborted");
					}
				}
				break;

			case APPS_DATA:
				if (system("readlink /data/app")) {
					ui_print("\nApps already in /data");
				} else {
					if (!system("readlink /data/app | grep cache")) {
						ui_print("\n- Apps are currently in\n- /cache/app");
					} else {
						ui_print("\n- Apps are currently in\n- SD card (ext partition)");
					}

					if (confirm_key("move your apps\nto /data/app")) {
						if (ensure_root_path_mounted("DATA:") == 0 && ensure_root_path_mounted("SDEXT:") == 0) {
							!system("appsto data") ? ui_print("\nApps successfully moved!") \
									    : ui_print("\nError moving apps");
						} else {
							ui_print("\nCan't mount /data or /sdcard");
						}
					} else {
						ui_print("\nApps2SD move aborted");
					}
				}
				break;

			case KEY_DREAM_BACK:
				deletion = 0;
				return;
		}
	}
	deletion = 0;
}

//32 character length
static void
prompt_and_wait()
{
    static char* headers[] = { 	" Android System Recovery " EXPAND(RECOVERY_API_VERSION) "",
                		        "  SDX Samsung Moment SPH-M900",
								"",
                        		"Use Up/Down and OK to select",
					"",
                        		NULL };
#define ITEM_REBOOT		0
#define ITEM_APPLY_ZIP		1
#define ITEM_PARTITIONS		2
#define ITEM_FILE_BROWSE	3
#define ITEM_MOUNT_OPTIONS	4
#define ITEM_SD_PARTITION	5
#define ITEM_ADVANCED_OPTS	6
#define ITEM_CONSOLE       	7

	static char* items[] = {"Reboot options",
							"Apply zip from SD Card",
							"Backup, Restore, Flash",
							"File browser",
							"Mount options",
							"Partition SD Card",
							"Advanced Options",
							"Go to Console",
							NULL };
    for (;;) {
	finish_recovery(NULL);
	ui_reset_progress();

	int chosen_item = get_menu_selection(headers, items), reboot;
	deletion = 0;

        switch (chosen_item) {
	        case ITEM_REBOOT:
		    reboot = reboot_options();
		    if (reboot) {
			do_reboot = reboot;
			return;
			}
		    break;

	        case ITEM_APPLY_ZIP:
	                choose_update_file();
	                break;
	                
	        case ITEM_PARTITIONS:
	        	partition_options();
	        	break;
		
		case ITEM_FILE_BROWSE:
			browse_files();
			break;

		case ITEM_MOUNT_OPTIONS:
			mount_options();
			break;

		case ITEM_SD_PARTITION:
			sd_part_options();
			break;

		case ITEM_ADVANCED_OPTS:
			advanced_menu();
			break;

	        case ITEM_CONSOLE:
	                ui_print("\n");
		    	do_reboot = 0;
		    	gr_exit();
		    	system("echo 1 > /sys/class/leds/keyboard-backlight/brightness");
	                return;
        }
    }
}

static void
print_property(const char *key, const char *name, void *cookie)
{
    fprintf(stderr, "%s=%s\n", key, name);
}

static void
check_for_updates(void)
{
    // must improve for all partitions
    if (!system("cat /sdcard/sdx/updates/update_ready | grep `md5sum /sdcard/sdx/updates/recovery.rfs | awk '{ print $1 }'`")) {
		ui_print("- Update found! Press HOME\n- to install");
		if (ui_wait_key() == KEY_DREAM_HOME) {
			if (system("/sbin/flash_image recovery /sdcard/sdx/updates/recovery.rfs")) {
				ui_print("\n\nUpdate unsuccessful. Press\nany key to continue");
			} else {
				ui_print("\n\nUpdate successful! Press\nany key to reboot to recovery");
				system("rm -f /sdcard/sdx/updates/update_ready");
				system("/sbin/reboot recovery");
			}
			ui_wait_key();
		}
    }
}

int
main(int argc, char **argv)
{
    time_t start = time(NULL);

    // If these fail, there's not really anywhere to complain...
    freopen(TEMPORARY_LOG_FILE, "a", stdout); setbuf(stdout, NULL);
    freopen(TEMPORARY_LOG_FILE, "a", stderr); setbuf(stderr, NULL);
    fprintf(stderr, "Starting recovery on %s", ctime(&start));

    tcflow(STDIN_FILENO, TCOOFF);
    
//    char prop_value[PROPERTY_VALUE_MAX];
//    property_get("ro.build.display.id", &prop_value, "not set");

    ui_init();
    get_args(&argc, &argv);

    int previous_runs = 0;
    const char *send_intent = NULL;
    const char *update_package = NULL;
    int wipe_data = 0, wipe_cache = 0;

    int arg;
    while ((arg = getopt_long(argc, argv, "", OPTIONS, NULL)) != -1) {
        switch (arg) {
        case 'p': previous_runs = atoi(optarg); break;
        case 's': send_intent = optarg; break;
        case 'u': update_package = optarg; break;
        case 'w': wipe_data = wipe_cache = 1; break;
        case 'c': wipe_cache = 1; break;
        case '?':
            LOGE("Invalid command argument\n");
            continue;
        }
    }

    fprintf(stderr, "Command:");
    for (arg = 0; arg < argc; arg++) {
        fprintf(stderr, " \"%s\"", argv[arg]);
    }
    fprintf(stderr, "\n\n");

    property_list(print_property, NULL);
    fprintf(stderr, "\n");

#if TEST_AMEND
    test_amend();
#endif

    RecoveryCommandContext ctx = { NULL };
    if (register_update_commands(&ctx)) {
        LOGE("Can't install update commands\n");
    }

    int status = INSTALL_SUCCESS;

    if (update_package != NULL) {
        status = install_package(update_package);
        if (status != INSTALL_SUCCESS) ui_print("Installation aborted.\n");
    } else if (wipe_data || wipe_cache) {
        if (wipe_data && erase_root("DATA:")) status = INSTALL_ERROR;
        if (wipe_cache && erase_root("CACHE:")) status = INSTALL_ERROR;
        if (status != INSTALL_SUCCESS) ui_print("Data wipe failed.\n");
    } else {
        status = INSTALL_ERROR;  // No command specified
    }

    if (status != INSTALL_SUCCESS) ui_set_background(BACKGROUND_ICON_ERROR);

// Forcystos edits to recovery boot    
    system("echo 0 > /sys/class/leds/keyboard-backlight/brightness");
    ensure_root_path_mounted("SYSTEM:");
    ensure_root_path_mounted("DATA:");
    ensure_root_path_mounted("SDCARD:");
// end edits

    // check_for_updates(); needs to be improved and I already got a proper method

    if (status != INSTALL_SUCCESS) prompt_and_wait();

    // If there is a radio image pending, reboot now to install it.
    maybe_install_firmware_update(send_intent);

    // Otherwise, get ready to boot the main system...
    finish_recovery(send_intent);
    sync();
    if (do_reboot)
    {
    	ui_print("Rebooting...\n");
	sync();
	if (do_reboot == 2) reboot(RB_POWER_OFF);
	reboot(RB_AUTOBOOT);
    }
	
    tcflush(STDIN_FILENO, TCIOFLUSH);	
    tcflow(STDIN_FILENO, TCOON);
	
    return EXIT_SUCCESS;
}
