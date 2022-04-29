TARGET_BINS=maildirmerge maildirsizes maildircheck maildirreconstruct

EXTRA_BINS=maildirduperem

server_types=servertypes server_courier

MODS_maildirmerge=maildirmerge $(server_types)
MODS_maildirsizes=maildirsizes
MODS_maildircheck=maildircheck filetools
MODS_maildirreconstruct=maildirreconstruct filetools $(server_types)

include Makefile.inc
