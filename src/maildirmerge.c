#define _GNU_SOURCE

#include <stdlib.h>
#include <stdio.h>
#include <unistd.h>
#include <getopt.h>
#include <fcntl.h>
#include <sys/stat.h>
#include <errno.h>
#include <string.h>
#include <dirent.h>

#include "servertypes.h"
#include "filetools.h"

static const char* progname = NULL;
static int force = 0, dry_run = 0, pop3_merge_seen = 0;
static int pop3_uidl = 0;
static int subscribe = 0;
static const char* pop3_redirect = NULL;

static
void __attribute__((noreturn)) usage(int x)
{
	FILE *o = x ? stderr : stdout;

	fprintf(o, "USAGE: %s [options] destfolder sourcefolder [...]\n", progname);
	fprintf(o, "IMPORTANT:  sourcefolders will be migrated (merged) into destfolder.\n");
	fprintf(o, "  The emails will be REMOVED from the sourcefolders.\n");
	fprintf(o, "OPTIONS:\n");
	fprintf(o, "  -f|--force\n");
	fprintf(o, "    Enable force mode, permits overriding certain safeties.\n");
	fprintf(o, "  -n|--dry-run\n");
	fprintf(o, "    Dry-run only, output what would be done without doing it.\n");
	fprintf(o, "  --pop3-uidl\n");
	fprintf(o, "    Do attempt to sync POP3 UIDL values.\n");
	fprintf(o, "  --pop3-redirect foldername\n");
	fprintf(o, "    Redirect previously seen messages for POP3 to an alternative IMAP folder.\n");
	fprintf(o, "  --pop3-merge-seen\n");
	fprintf(o, "    Ignore seen status when POP3 detected proceed to merge all mail into the destination.\n");
	fprintf(o, "    This is mutually exclusive with --pop3-redirect.\n");
	fprintf(o, "    By default any previously seen messages are left behind if the destination\n");
	fprintf(o, "    is detected to have POP3 active.  It doesn't care when last POP3 has been used currently.\n");
	fprintf(o, "  --subscribe\n");
	fprintf(o, "    For unknown folder sources (ie, we're unable to check if the folder is subscribed), auto subscribe.\n");
	fprintf(o, "    NOTE:  This only takes effect if the source maildir type is unknown/unsupported.\n");
	fprintf(o, "  -h|--help\n");
	fprintf(o, "    This help text.\n");
	exit(x);
}

#define out_error_if(x, f, ...) do { if (x) { fprintf(stderr, f ": %s\n", ## __VA_ARGS__, strerror(errno)); goto out; } } while(0)
static
void maildir_merge(const char* target, int targetfd, struct maildir_type_list *target_types,
		const char* source)
{
	struct maildir_type_list *source_types, *ti;
	const struct maildir_type *stype = NULL;
	int sourcefd = get_maildir_fd(source);
	int sfd = -1, tfd = -1, rfd = -1;
	char *redirectname = NULL;
	struct stat st;
	int is_pop3 = 0;
	void *stype_pvt = NULL;

	DIR* dir;
	struct dirent *de;

	if (sourcefd < 0)
		return;

	source_types = maildir_find_type(source);
	if (source_types) {
		if (source_types->next) {
			fprintf(stderr, "%s: multiple types triggered, not proceeding for safety.\n",
					source);
			goto out;
		}

		stype = source_types->type;
		maildir_type_list_free(source_types);

		if (stype->open)
			stype_pvt = stype->open(source, sourcefd);
	}

	printf("Merging %s (%s) into %s.\n", source, stype ? stype->label : "no type detected", target);

	for (ti = target_types; ti && !is_pop3; ti = ti->next)
		if (ti->type->is_pop3)
			is_pop3 = ti->type->is_pop3(ti->pvt);

	if (is_pop3)
		printf("Target folder is used for POP3.\n");

	/* For the new folder we couldn't care less, just rename from source into dest */
	sfd = openat(sourcefd, "new", O_RDONLY);
	out_error_if(sfd < 0, "%s/new", source);

	tfd = openat(targetfd, "new", O_RDONLY);
	out_error_if(tfd < 0, "%s/new", target);

	dir = fdopendir(sfd);
	out_error_if(!dir, "%s/new", source);

	while ((de = readdir(dir))) {
		switch (de->d_type) {
			case DT_REG:
				break;
			case DT_UNKNOWN:
				if (fstatat(sfd, de->d_name, &st, 0) < 0) {
					fprintf(stderr, "%s/cur/%s: %s\n", source, de->d_name, strerror(errno));
					continue;
				}

				if ((st.st_mode & S_IFMT) == S_IFREG)\
					break;
				/* FALLTHROUGH */
			default:
				continue;
		}

		maildir_move(sfd, source, tfd, target, "new", de->d_name, dry_run);
	}
	closedir(dir); dir = NULL; sfd = -1;
	close(tfd); tfd = -1;

	/* the cur folder is somewhat more involved, there are IMAP UID values, as well
	 * as POP3 related work here.
	 *
	 * Firstly, we may or may not bring over the POP3 UIDL values (usually pointless).
	 *
	 * Secondly, we may leave behind, redirect or merge anyway messages that have already
	 * been seen (in short:
	 * leave behind - just ignore these.
	 * redirect - create a new maildir folder and dump these messages in it's new/
	 *
	 * These two 'functions' really aught to be merged.
	 **/
	sfd = openat(sourcefd, "cur", O_RDONLY);
	out_error_if(sfd < 0, "%s/cur", source);

	tfd = openat(targetfd, "cur", O_RDONLY);
	out_error_if(tfd < 0, "%s/cur", target);

	dir = fdopendir(sfd);
	out_error_if(!dir, "%s/cur", source);

	while ((de = readdir(dir))) {
		switch (de->d_type) {
			case DT_REG:
				break;
			case DT_UNKNOWN:
				if (fstatat(sfd, de->d_name, &st, 0) < 0) {
					fprintf(stderr, "%s/cur/%s: %s\n", source, de->d_name, strerror(errno));
					continue;
				}

				if ((st.st_mode & S_IFMT) == S_IFREG)\
					break;
				/* FALLTHROUGH */
			default:
				continue;
		}

		if (!is_pop3 || pop3_merge_seen || !message_seen(de->d_name)) {
			maildir_move(sfd, source, tfd, target, "cur", de->d_name, dry_run);
			if (pop3_uidl) {
				if (!stype || !stype->pop3_get_uidl) {
					fprintf(stderr, "UIDL transfer requested but source doesn't support UIDL retrieval.\n");
				} else {
					char *basename = strdupa(de->d_name);
					char *t = strchr(basename, ':');
					if (t)
						*t = 0; /* truncate the fields out of there. */
					char *uidl = stype->pop3_get_uidl(stype_pvt, basename);

					if (uidl) {
						if (dry_run) {
							printf("Setting UIDL to %s\n", uidl);
						} else {
							for (ti = target_types; ti; ti = ti->next) {
								if (ti->type->pop3_set_uidl)
									ti->type->pop3_set_uidl(ti->pvt, basename, uidl);
							}
						}
						free(uidl);
					}
				}
			}
		} else if (pop3_redirect) {
			if (rfd < 0) {
				rfd = maildir_create_sub(targetfd, target, pop3_redirect, dry_run);
				if (rfd < 0)
					exit(1);
				int t = openat(rfd, "cur", O_RDONLY);
				close(rfd);
				rfd = t;
				if (rfd < 0) {
					fprintf(stderr, "%s/%s/cur: %s\n", target, pop3_redirect, strerror(errno));
					exit(1);
				}
				asprintf(&redirectname, "%s/%s", target, pop3_redirect);
			}

			maildir_move(sfd, source, rfd, redirectname, "cur", de->d_name, dry_run);
		} else if (dry_run) {
			printf("%s/cur/%s: left behind (seen, target is POP3, no redirect).\n",
					source, de->d_name);
		}
	}

	closedir(dir); dir = NULL; sfd = -1;
	close(tfd); tfd = -1;
	if (rfd >= 0) {
		close(rfd);
		rfd = -1;
	}

	/* at this point, we scan for sub-folders, those are folders starting with
	 * ., which isn't . or .., at which point we create the sub-folders, and
	 * recursively merge into them. */
	dir = fdopendir(sourcefd);
	if (!dir) {
		perror(source);
		goto out;
	}

	while ((de = readdir(dir))) {
		switch (de->d_type) {
			case DT_DIR:
				break;
			case DT_UNKNOWN:
				if (fstatat(sfd, de->d_name, &st, 0) < 0) {
					fprintf(stderr, "%s/cur/%s: %s\n", source, de->d_name, strerror(errno));
					continue;
				}

				if ((st.st_mode & S_IFMT) == S_IFDIR)
					break;
				/* FALLTHROUGH */
			default:
				continue;
		}
		if (de->d_name[0] != '.' || strcmp(de->d_name, ".") == 0 || strcmp(de->d_name, "..") == 0)
			continue;

		printf("sub folder: %s\n", de->d_name);

		if (fstatat(targetfd, de->d_name, &st, 0) == 0) {
			/* we know both the source and destination exist, so we can just go recursively here */
			char *sub_target;
			char *sub_source;
			int sub_target_fd = get_maildir_fd_at(targetfd, de->d_name);
			if (sub_target_fd < 0)
				continue;

			if (asprintf(&sub_target, "%s/%s", target, de->d_name) < 0) {
				fprintf(stderr, "memory error trying to merge %s from %s to %s.\n",
						de->d_name, source, target);
				close(sub_target_fd);
				continue;
			}
			if (asprintf(&sub_source, "%s/%s", source, de->d_name) < 0) {
				fprintf(stderr, "memory error trying to merge %s from %s to %s.\n",
						de->d_name, source, target);
				free(sub_target);
				close(sub_target_fd);
				continue;
			}

			struct maildir_type_list *sub_target_types = maildir_find_type(sub_target);
			for (ti = sub_target_types; ti; ti = ti->next) {
				printf("%s: Detected type: %s\n", sub_target, ti->type->label);
				if (ti->type->open)
					ti->pvt = ti->type->open(sub_target, sub_target_fd);
			}

			maildir_merge(sub_target, sub_target_fd, sub_target_types, sub_source);

			maildir_type_list_free(sub_target_types);
			free(sub_source);
			free(sub_target);
			close(sub_target_fd);

		} else if (errno == ENOENT) {
			/* it doesn't exist, so we can simply rename into, and then check subscriptions */
			maildir_move(sourcefd, source, targetfd, target, "", de->d_name, dry_run);

			if (stype ? stype->imap_is_subscribed && stype->imap_is_subscribed(stype_pvt, de->d_name) : subscribe) {
				if (dry_run) {
					printf("Will subscribe to %s on target.\n", de->d_name);
				} else {
					for (ti = target_types; ti; ti = ti->next) {
						if (ti->type->imap_subscribe)
							ti->type->imap_subscribe(ti->pvt, de->d_name);
					}
				}
			}
		} else {
			fprintf(stderr, "%s/%s: %s\n", target, de->d_name, strerror(errno));
		}
	}
	closedir(dir); dir = NULL; sourcefd = -1;

out:
	if (stype && stype->close)
		stype->close(stype_pvt);

	if (dir)
		closedir(dir);

	close(sourcefd);
	if (sfd >= 0)
		close(sfd);
	if (tfd >= 0)
		close(tfd);
	if (rfd >= 0)
		close(rfd);

	if (redirectname)
		free(redirectname);
}

static struct option options[] = {
	{ "dry-run",		no_argument,		NULL,	'd' },
	{ "force",			no_argument,		NULL,	'f' },
	{ "help",			no_argument,		NULL,	'h' },
	{ "pop3-redirect",	required_argument,	NULL,	'r' },
	{ "pop3-merge-seen",no_argument,		&pop3_merge_seen, 1 },
	{ "pop3-uidl",		no_argument,		&pop3_uidl, 1 },
	{ "subscribe",		no_argument,		&subscribe, 1 },
	{ NULL, 0, NULL, 0 },
};

int main(int argc, char** argv)
{
	int c, targetfd;
	const char* target;
	struct maildir_type_list *target_types, *ti;

	progname = *argv;

	while ((c = getopt_long(argc, argv, "fhn", options, NULL)) != -1) {
		switch (c) {
		case 0:
			break;
		case 'f':
			force = 1;
			break;
		case 'n':
			dry_run = 1;
			break;
		case 'r':
			pop3_redirect = optarg;
			break;
		case 'h':
			usage(0);
		case '?':
			fprintf(stderr, "Unrecognised option encountered.\n");
			usage(1);
		default:
			fprintf(stderr, "Option not implemented: %c.\n", c);
			exit(1);
		}
	}

	if (pop3_merge_seen && pop3_redirect) {
		fprintf(stderr, "You can't specify both --pop3-redirect and --pop3-ignore\n");
		usage(1);
	}

	if (!argv[optind]) {
		fprintf(stderr, "No target folder specified!\n");
		usage(1);
	}

	target = argv[optind++];
	targetfd = get_maildir_fd(target);
	if (targetfd < 0)
		return 1;

	target_types = maildir_find_type(target);
	if (!target_types) {
		fprintf(stderr, "Error detecting destination folder type(s).\n");
		if (!force) {
			fprintf(stderr, "Use --force to proceed as bare maildir.\n");
			return 1;
		}
	}

	for (ti = target_types; ti; ti = ti->next) {
		printf("%s: Detected type: %s\n", target, ti->type->label);
		if (ti->type->open)
			ti->pvt = ti->type->open(target, targetfd);
	}

	while (argv[optind])
		maildir_merge(target, targetfd, target_types, argv[optind++]);

	for (ti = target_types; ti; ti = ti->next) {
		if (ti->type->close)
			ti->type->close(ti->pvt);
	}

	maildir_type_list_free(target_types);

	return 0;
}
