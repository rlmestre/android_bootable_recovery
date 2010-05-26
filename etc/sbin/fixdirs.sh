#!/system/bin/sh

# move backups
if [ ! -d "/sdcard/sdx/backup" ];
	then
		mkdir -p /sdcard/sdx/backup
		cat "Backups directory created" >> /tmp/recovery.log
fi

if [ -d "/sdcard/backups" ];
	then
		mv /sdcard/backups/* /sdcard/sdx/backup/
		rmdir /sdcard/backups
		cat "Old backups dir migrated and removed" >> /tmp/recovery.log
fi

# move updates
if [ ! -d "/sdcard/sdx/updates" ];
	then
		mkdir -p /sdcard/sdx/updates
		cat "Updates directory created" >> /tmp/recovery.log
fi

if [ -d "/sdcard/updates" ];
	then
		mv /sdcard/updates/* /sdcard/sdx/updates/
		rmdir /sdcard/updates
		cat "Old updates dir migrated and removed" >> /tmp/recovery.log
fi

# move zips
if [ ! -d "/sdcard/sdx/zip" ];
	then
		mkdir -p "/sdcard/sdx/zip"
		cat "Zip directory created" >> /tmp/recovery.log
fi

if [ -d "/sdcard/updates" ];
	then
		mv /sdcard/*.zip "/sdcard/sdx/zip/"
		cat "Old zip dir migrated" >> /tmp/recovery.log
fi
