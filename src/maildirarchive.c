#define _GNU_SOURCE

#include <getopt.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <fcntl.h>
#include <errno.h>
#include <string.h>
#include <time.h>
#include <dirent.h>
#include <sys/stat.h>
#include <stdbool.h>
#include <ctype.h>

#include "servertypes.h"

#define lerror(fmt, ...) fprintf(stderr, fmt ": %s.\n", ##__VA_ARGS__, strerror(errno))

#define DEFAULT_MAXAGE		"1 year ago"

static const char* progname = NULL;
static int dry_run = 0;
static const char * subsources[] = { "new", "cur", NULL };

static
time_t maxage2time(const char* maxage)
{
	int p[2]; // 0 read, 1 write.
	FILE* fp;
	pid_t pid;
	time_t res = 0;
	if (pipe(p) < 0) {
		perror("pipe");
		exit(1);
	}

	pid = fork();
	if (pid < -1) {
		perror("fork");
		exit(1);
	}

	if (pid == 0) {
		char* args[] = {
			"date",
			"+%s",
			"-d",
			strdupa(maxage),
			NULL,
		};
		/* stdin */
		int t = open("/dev/null", O_RDONLY);
		dup2(t, 0);
		close(t);
		/* stdout */
		dup2(p[1], 1);
		/* read end */
		close(p[0]);

		execvp(*args, args);
		perror("execvp(date)");
		exit(1);
	}

	close(p[1]);
	fp =  fdopen(p[0], "r");
	if (fscanf(fp, "%lu", &res) != 1) {
		fprintf(stderr, "Error reading from date sub-process.\n");
		exit(1);
	}
	fclose(fp);

	printf("Archiving email older than: %s", ctime(&res));

	return res;
}

struct folder_cache_entry {
	char *foldername;
	int folderfd;
	struct folder_cache_entry *next;
};

static
bool valid_foldername(const char* fldrname)
{
	if (!fldrname)
		return false;
	if (*fldrname != '.')
		return false;
	if (strchr(fldrname, '/'))
		return false;
	/* Not a strict requirement, but let's avoid some issues out of hand */
	while (*fldrname)
		if (!isprint(*fldrname++))
			return false;
	return true;
}

static
int get_folderfd(const char* fldrname, int basefd, struct maildir_type_list* stype)
{
	// keep re-sorting according to most recently used, on the assumption that
	// we will typically get files linked into the dirent tree in some ordering
	// based on date/time, resulting in least recently used being most
	// required.  This could be very wrong.  But we also don't expect more than
	// a few tens of entries here.
	static struct folder_cache_entry *head = NULL;

	if (!fldrname) {
		while (head) {
			struct folder_cache_entry *tmp = head->next;
			free(head->foldername);
			close(head->folderfd);
			free(head);
			head = tmp;
		}
		return -1;
	} else {
		struct folder_cache_entry *cur, **_cur;
		for (_cur = &head; *_cur; _cur = &(*_cur)->next) {
			cur = *_cur;
			if (strcmp(cur->foldername, fldrname) == 0) {
				*_cur = cur->next;
				cur->next = head;
				head = cur;
				return cur->folderfd;
			}
		}
		// no matching entry found
		int fd = openat(basefd, fldrname, O_RDONLY);
		if (fd < 0) {
			if (errno != ENOENT)
				return -1;

			mode_t m = 0700;
			uid_t u = 0;
			gid_t g = 0;
			struct stat st;
			if (fstat(basefd, &st) == 0) {
				m = st.st_mode; /* attempt to clone from parent */
				if (geteuid() == 0) {
					/* we can chown() */
					u = st.st_uid;
					g = st.st_gid;
				}
			}
			if (mkdirat(basefd, fldrname, m) < 0)
				return -1;
			if (u || g)
				fchownat(basefd, fldrname, u, g, 0);
			fd = openat(basefd, fldrname, O_RDONLY);
			if (fd < 0)
				return -1;

			while (stype) {
				if (stype->type->imap_subscribe) {
					if (!stype->pvt && stype->type->open)
						stype->pvt = stype->type->open(fldrname, basefd);
					if (stype->pvt)
						stype->type->imap_subscribe(stype->pvt, fldrname);
				}
				stype = stype->next;
			}

#define mksub(x)	do { if (mkdirat(fd, x, m) < 0) { close(fd); return -1; } if (u || g) fchownat(fd, x, u, g, 0); } while(0)
			mksub("cur");
			mksub("new");
			mksub("tmp");
#undef mksub

			int t = openat(fd, "maildirfolder", O_CREAT, 0600);
			if (t >= 0) {
				fchownat(t, "", u, g, AT_SYMLINK_NOFOLLOW | AT_EMPTY_PATH);
				close(t);
			}
		}

		struct folder_cache_entry * ce = malloc(sizeof(*ce));
		ce->foldername = strdup(fldrname);
		ce->folderfd = fd;
		ce->next = head;
		head = ce;
		return ce->folderfd;
	}
}

static
void __attribute__((noreturn)) usage(int x)
{
	FILE *o = x ? stderr : stdout;

	fprintf(o, "USAGE: %s [options] root_folder [...]\n", progname);
	fprintf(o, "IMPORTANT:  sourcefolders will be migrated (merged) into destfolder.\n");
	fprintf(o, "  The emails will be REMOVED from the sourcefolders.\n");
	fprintf(o, "OPTIONS:\n");
	fprintf(o, "  -f|--format folder_format\n");
	fprintf(o, "    The format used to construct the target folder names.  Must comply with\n");
	fprintf(o, "    standard maildir format, in other words:\n");
	fprintf(o, "     - name must start with a .\n");
	fprintf(o, "     - not contain a /\n");
	fprintf(o, "    The format will be handed to strftime(3), please refer to the man page for\n");
	fprintf(o, "    details of %% escapes.\n");
	fprintf(o, "  -n|--dry-run\n");
	fprintf(o, "    Dry-run only, output what would be done without doing it.\n");
	fprintf(o, "  -s|--sourcefolder sourcefolder\n");
	fprintf(o, "    If archiving should be performed on a source subfolder rather than INBOX\n");
	fprintf(o, "  -m|--maxage string\n");
	fprintf(o, "    Maximum age of emails to retain in source folder, this is passed to the\n");
	fprintf(o, "    date CLI tool using date -d 'string' - so please verify this usage.\n");
	fprintf(o, "    defaults to '%s'.\n", DEFAULT_MAXAGE);
	fprintf(o, "  -R|--replace\n");
	fprintf(o, "    Do NOT use REPLACE_NOREPLACE.  This option can potentially destroy email,\n");
	fprintf(o, "    as an extra safety a stat() call will be made prior to rename, and if the\n");
	fprintf(o, "    target file exists will be skipped.  This is racey, not to mention bad for performance.\n");
	fprintf(o, "  -S|--subscribe\n");
	fprintf(o, "    Auto-subscribe to newly created folders.\n");
	fprintf(o, "  -h|--help\n");
	fprintf(o, "    Enable force mode, permits overriding certain safeties.\n");
	exit(x);
}

static struct option options[] = {
	{ "dry-run",		no_argument,		NULL,	'n' },
	{ "format",			required_argument,	NULL,	'f' },
	{ "sourcefolder",	required_argument,	NULL,	's' },
	{ "maxage",			required_argument,	NULL,	'm' },
	{ "replace",		no_argument,		NULL,	'R' },
	{ "subscribe",		no_argument,		NULL,	'S' },
	{ NULL, 0, NULL, 0 },
};

int main(int argc, char** argv)
{
	int c, basefd = -1, sfd = -1;
	const char* sourcefolder = NULL, *format = NULL,
		  *base, *_maxage = DEFAULT_MAXAGE;
	char* sourcename = NULL;
	time_t maxage;
	unsigned rename_flags = RENAME_NOREPLACE;
	struct stat st;
	bool subscribe = false;
	struct maildir_type_list* stype = NULL;
	int archive_count = 0, archive_folder_count;

	progname = *argv;

	while ((c = getopt_long(argc, argv, "nf:s:m:R", options, NULL)) != -1) {
		switch (c) {
		case 0:
			break;
		case 'f':
			format = optarg;
			break;
		case 'n':
			dry_run = 1;
			break;
		case 's':
			sourcefolder = optarg;
			break;
		case 'm':
			_maxage = optarg;
			break;
		case 'R':
			rename_flags &= ~RENAME_NOREPLACE;
			break;
		case 'S':
			subscribe = true;
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

	if (!format) {
		fprintf(stderr, "--format is a required option.\n");
		usage(1);
	}

	maxage = maxage2time(_maxage);
	if (!maxage) {
		fprintf(stderr, "Error converting '%s' to a date and time structure.\n",
				_maxage);
		usage(1);
	}

	if (!argv[optind]) {
		fprintf(stderr, "At least one maildir should be specified.\n");
		usage(1);
	}

	while (argv[optind]) {
		base = argv[optind++];
		basefd = open(base, O_RDONLY /*dry_run ? O_RDONLY : O_RDWR */); // TODO: Do we need WR for mkdirat()?
		if (basefd < 0) {
			perror(base);
			goto errout;
		}

		if (subscribe) {
			stype = maildir_find_type(base);
			if (!stype) {
				fprintf(stderr, "%s: We need to be able to determine the folder type if we're to auto-subscribe.\n", base);
				goto errout;
			}
		}

		if (sourcefolder) {
			asprintf(&sourcename, "%s/%s", base, sourcefolder);
			sfd = openat(basefd, sourcefolder, O_RDONLY);
			if (sfd < 0) {
				perror(sourcename);
				goto errout;
			}
		} else {
			sourcename = strdup(base);
			sfd = dup(basefd);
		}

		archive_folder_count = 0;

		for (const char * const *_sfn = subsources; *_sfn; ++_sfn) {
			const char* sfn = *_sfn;
			char *endptr;
			int cfd = openat(sfd, sfn, O_RDONLY);
			if (cfd < 0) {
				lerror("%s/%s", sourcename, sfn);
				continue;
			}
			DIR* dir = fdopendir(cfd);
			struct dirent *de;

			printf("Archiving from %s/%s\n", sourcename, sfn);
			while ((de = readdir(dir))) {
				time_t filetime;
				char tfname[256];
				char tfname2[256];

				if (*de->d_name == '.')
					continue;
				if (de->d_type == DT_UNKNOWN) {
					static int warned = 0;
					if (!warned) {
						fprintf(stderr, "readdir() doesn't provide d_type, assuming everything is files to avoid costly stat() calls.\n");
						warned = 1;
					}
				} else if (de->d_type != DT_REG)
					continue; /* we only care about files, stuff here must be files */

				// filename should be structured as seconds_since_epoch.stuff, so we care
				// about the seconds here portion only.  The simplest is to convert as unsigned
				// int, and then verify that the failure ended at a .
				filetime = strtoul(de->d_name, &endptr, 10);

				if (endptr == de->d_name || !endptr || *endptr != '.') {
					fprintf(stderr, "Failed to extra timestamp from %s/%s/%s\n", sourcename, sfn, de->d_name);
					continue;
				}

				if (filetime >= maxage) {
					/* file is too young */
					continue;
				}

				if (!strftime(tfname, sizeof(tfname), format, localtime(&filetime)) || !valid_foldername(tfname)) {
					fprintf(stderr, "Error generating valid foldername from %s (%lu).  Cannot proceed\n", de->d_name, filetime);
					continue;
				}

				++archive_folder_count;
				if (dry_run) {
					printf("%s/%s/%s => %s/%s/%s/\n",
							sourcename, sfn, de->d_name, base, tfname, sfn);
					continue;
				}

				int tfd = get_folderfd(tfname, basefd, stype);
				if (tfd < 0) {
					lerror("%s/%s", base, tfname);
					continue;
				}

				/* ssize_t negative will become large positive when cast to size_t */
				if ((size_t)snprintf(tfname2, sizeof(tfname2), "%s/%s", sfn, de->d_name) >= sizeof(tfname2)) {
					fprintf(stderr, "Trucation error looking to rename %s/%s/%s into %s/%s/%s.\n",
							sourcename, sfn, de->d_name, base, tfname, sfn);
					continue;
				}

				if ((rename_flags & RENAME_NOREPLACE) == 0) {
					if (fstatat(tfd, tfname2, &st, 0) == 0) {
						errno = EEXIST;
						lerror("%s/%s/%s => %s/%s/%s/ (stat)",
							sourcename, sfn, de->d_name, base, tfname, sfn);
						continue;
					} else if (errno != ENOENT) {
						lerror("%s/%s/%s => %s/%s/%s/ (stat)",
							sourcename, sfn, de->d_name, base, tfname, sfn);
						continue;
					}
				}

				if (renameat2(cfd, de->d_name, tfd, tfname2, rename_flags) < 0) {
					lerror("%s/%s/%s => %s/%s/%s/",
							sourcename, sfn, de->d_name, base, tfname, sfn);
					if ((rename_flags & RENAME_NOREPLACE) != 0 && errno == EINVAL &&
						fstatat(tfd, tfname2, &st, 0) == -1 && errno == ENOENT)
					{
						fprintf(stderr, "We received EINVAL on rename using RENAME_NOREPLACE.  Possibly the filesystem doesn't like this, so please retry using (potentially dangerous) -R.\n");
						goto errout;
					}
				}
			}
			closedir(dir); /* also closes cfd */
		}
		printf("%s: Archived %d emails.\n", sourcename, archive_folder_count);

		archive_count += archive_folder_count;

		get_folderfd(NULL, -1, NULL);

		free(sourcename);
		sourcename = NULL;

		close(sfd);
		sfd = -1;

		close(basefd);
		basefd = -1;

		maildir_type_list_free(stype);
	}

	printf("Archived %d emails total.\n", archive_count);

	return 0;
errout:
	if (basefd >= 0)
		close(basefd);
	if (sfd >= 0)
		close(sfd);
	if (stype)
		maildir_type_list_free(stype);

	get_folderfd(NULL, -1, NULL);
	free(sourcename);

	return 1;
}
