#include "filetools.h"

#define _GNU_SOURCE

#include <stdio.h>
#include <getopt.h>
#include <fcntl.h>
#include <unistd.h>
#include <stdlib.h>
#include <string.h>
#include <errno.h>
#include <dirent.h>
#include <sys/stat.h>
#include <stdbool.h>

#define MAX_STAT_ENOENT_RETRY		10

static const char * progname;
static const char * maildir_subs[] = { "cur", "new", "-tmp", NULL };
static const char * valid_flags = "PRSTDFabcdefghijklmnopqrstuvwxyz";

static int fix_fixable = false;
static int fixed = 0;

/* tmp/ needs not be scanned.
 * ordering critical as stuff gets rename()d from new/ to cur/,
 * and thus we need to get filenames from cur/ first else we
 * can see a filename first in new/ and then in cur/ triggering an error
 * - indicates we don't need to scan.
 * + indicates that we must have :2, and optional flags.
 **/

struct msg_list {
	char* basename; /* unique */
	char **fullnames; /* NULL terminated */
	struct msg_list *next;
};

static
void msg_list_free(struct msg_list *m)
{
	struct msg_list *t;
	char **ff;
	while (m) {
		t = m->next;

		free(m->basename);
		for (ff = m->fullnames; *ff; ++ff)
			free(*ff);
		free(m->fullnames);
		free(m);

		m = t;
	}
}

static
void msg_list_add(struct msg_list **mlist, const char* sub, const char* fn)
{
	const char* base = fn;
	const char* colon = strchr(fn, ':');
	if (colon)
		base = strndupa(fn, colon - fn);

	/* insert in ASCII order, this is probably the worst choice */
	while (*mlist && strcmp((*mlist)->basename, base) < 0)
		mlist = &(*mlist)->next;

	if (*mlist && strcmp((*mlist)->basename, base) == 0) {
		/* error condition, base is not unique, just add to the fullnames. */
		int i = 0;
		while ((*mlist)->fullnames[i++])
			;
		(*mlist)->fullnames = realloc((*mlist)->fullnames, sizeof(*(*mlist)->fullnames) * (i+1));
		asprintf(&(*mlist)->fullnames[i-1], "%s/%s", sub, fn);
		(*mlist)->fullnames[i] = NULL;
	} else {
		struct msg_list *n = malloc(sizeof(struct msg_list));
		n->basename = strdup(base);
		n->fullnames = malloc(sizeof(*n->fullnames) * 2);
		asprintf(&n->fullnames[0], "%s/%s", sub, fn);
		n->fullnames[1] = NULL;
		n->next = *mlist;
		*mlist = n;
	}
}

static
void __attribute__((unused)) msg_list_dump(const struct msg_list *m)
{
	while (m) {
		printf("base: %s\n", m->basename);
		char** fn = m->fullnames;
		while (*fn)
			printf(" - %s\n", *fn++);
		m = m->next;
	}
}

/* This is designed to "accomodate" a glusterfs bug w.r.t. linkto files that
 * doesn't properly heal. Since we are VERY certain that we got a readdir()
 * entry prior to this, we know that we should NEVER get ENOENT, so keep retrying
 * a few times until we don't.  Output a warning to STDERR indicating number of rounds.
 **/
static
int myfstatat(int dirfd, const char *restrict pathname, struct stat *restrict statbuf, int flags)
{
	int r;
	int retries = MAX_STAT_ENOENT_RETRY;
	do {
		r = fstatat(dirfd, pathname, statbuf, AT_SYMLINK_NOFOLLOW | flags);
	} while (r < 0 && errno == ENOENT && --retries);
	if (retries < MAX_STAT_ENOENT_RETRY) {
		fprintf(stderr, "\nWe had %d ENOENT failures for stat(%s).\n",
				MAX_STAT_ENOENT_RETRY - retries, pathname);
	}
	return r;
}

static
bool chrinstr(char c, const char* head, const char* tail)
{
	while (head < tail)
		if (c == *head++)
			return true;

	return false;
}

/* We cannot assume alphabetic order here since fixing thereof may potentially
 * have failed */
/* Note that the exact same set of flags is NOT a subset of the flags itself
 * such that if we have exact duplicate filenames (as is possible through a
 * corrupted glusterfs filesystem) we won't nuke the only copy by accident.
 */
static
bool flags_subset_of(const char* fn1, const char* fn2)
{
	const char* t;
	const char* fs1 = strstr(fn1, ":2,");
	const char* fs2 = strstr(fn2, ":2,");

	if (!fs2)
		return false;

	/* if fs1 doesn't have flags it's *obviously* a subset of fs2's flags */
	if (!fs1)
		return true;

	/* skip over the markers. */
	fs1 += 3;
	fs2 += 3;

	const char* fs1t = fs1;
	while (*fs1t && *fs1t != ',')
		++fs1t;

	const char* fs2t = fs2;
	while (*fs2t && *fs2t != ',')
		++fs2t;

	/* We WANT the tags for fn1 to be fewer than for fn2.  If that holds,
	 * there is a chance, this is a quick out */
	if ((fs1t - fs1) >= (fs2t - fs2))
		return false;

	/* all tags in fn1 must be in fn2 */
	for (t = fs1; t < fs1t; t++)
		if (!chrinstr(*t, fs2, fs2t))
			return false;

	/* at least one tag in fn2 must not be in fn1 */
	for (t = fs2; t < fs2t; t++)
		if (!chrinstr(*t, fs1, fs1t))
			return true;

	return false;

}

static
bool copy_prefer_over(int fd, const char* a, const char* b)
{
	if (strncmp(a, "cur/", 4) == 0 && strncmp(b, "new/", 4) == 0) {
		/* we prefer cur/ over new/, however, we still need files_identical check */
	} else if (!flags_subset_of(b, a)) {
		return false;
	}

	return !!files_identical(fd, a, NULL, fd, b, NULL);
}

#define add_error(ec, fmt, ...) do { printf("\n" fmt, ## __VA_ARGS__); fflush(stdout); ++(ec); } while(0)

#define check_ownership(fd, path, st, ec, fmt, ...) do { \
	if (myfstatat(fd, path, &st, AT_EMPTY_PATH) < 0) { \
		add_error(ec, "fstatat(" fmt "): %s - cannot check ownership", ## __VA_ARGS__, strerror(errno)); \
	} else { \
		errno = 0; \
		if (st.st_uid != uid) \
			add_error(ec, fmt ": Wrong ownership, uid=%lu is not %lu.", ## __VA_ARGS__, (unsigned long)st.st_uid, (unsigned long)uid); \
		if (st.st_gid != gid) \
			add_error(ec, fmt ": Wrong group, gid=%lu is not %lu.", ## __VA_ARGS__, (unsigned long)st.st_gid, (unsigned long)gid); \
		if (fix_fixable && (st.st_uid != uid || st.st_gid != gid)) { \
			fchownat(fd, path, uid, gid, AT_SYMLINK_NOFOLLOW | AT_EMPTY_PATH); \
			fixed++; \
		} \
	} \
} while(0)

static
int check_fdpath(int fd, const char* rpath, uid_t uid, gid_t gid)
{
	const char ** sp = maildir_subs;
	const char * subname;
	int ec = 0, sfd;
	printf("%s:", rpath + 1 /* leading . */); fflush(stdout);
	int noscan;
	int forceflags;
	DIR *dir;
	struct dirent *de;
	struct msg_list *mlist = NULL, *slist;
	struct stat st;

	if (fstatat(fd, "maildirfolder", &st, 0) < 0) {
		if (errno != ENOENT) {
			add_error(ec, "maildirfolder: %s", strerror(errno));
		} else if (*rpath) {
			add_error(ec, "Expected to find a file called maildirfolder");
			if (fix_fixable) {
				int t = openat(fd, "maildirfolder", O_CREAT, 0600);
				if (t >= 0) {
					fchownat(t, "", uid, gid, AT_SYMLINK_NOFOLLOW | AT_EMPTY_PATH);
					close(t);
				}
			}
		}
	} else if (!*rpath) {
		add_error(ec, "Did not expect to find a file called maildirfolder");
	} else {
		if (st.st_size)
			add_error(ec, "maildirfolder file should be empty.");
		if (st.st_uid != uid)
			add_error(ec, "maildirfolder: Wrong ownership, uid=%lu is not %lu.", (unsigned long)st.st_uid, (unsigned long)uid);
		if (st.st_gid != gid)
			add_error(ec, "maildirfolder: Wrong group, gid=%lu is not %lu.", (unsigned long)st.st_gid, (unsigned long)gid);
	}

	check_ownership(fd, "", st, ec, ".");
	for (sp = maildir_subs; *sp; ++sp) {
		subname = *sp;
		noscan = *subname == '-';
		if (noscan)
			++subname;
		forceflags = *subname == '+';
		if (forceflags)
			++subname;
		sfd = openat(fd, subname, O_RDONLY);
		if (sfd < 0) {
			add_error(ec, "%s: %s.", subname, strerror(errno));
			if (errno == ENOENT && fix_fixable) {
				mkdirat(fd, subname, 0700);
				sfd = openat(fd, subname, O_RDONLY);
				if (sfd >= 0) {
					fixed++;
					fchownat(sfd, "", uid, gid, AT_SYMLINK_NOFOLLOW | AT_EMPTY_PATH);
				}
			}
			if (sfd < 0)
				continue;
		}

		check_ownership(sfd, "", st, ec, "%s", subname);

		if (noscan) {
			close(sfd);
			continue;
		}

		dir = fdopendir(sfd);
		if (!dir) {
			add_error(ec, "%s: %s", subname, strerror(errno));
			close(sfd);
		} else {
			while ((de = readdir(dir))) {
				if (strcmp(de->d_name, ".") == 0 || strcmp(de->d_name, "..") == 0)
					continue;
				check_ownership(sfd, de->d_name, st, ec, "%s/%s", subname, de->d_name);

				const char* ssize = strstr(de->d_name, "S=");

				if (errno == 0 && ssize) {
					off_t sz = strtoul(ssize + 2, NULL, 10);
					if (sz != st.st_size) {
						add_error(ec, "%s/%s: found file to have size %lu, expected S=%lu.",
								subname, de->d_name, st.st_size, sz);
					}
				}

				const char* colon = strchr(de->d_name, ':');

				if (!colon) {
					if (forceflags)
						add_error(ec, "%s/%s: in folder that requires flags (:2, in filename).\n",
								subname, de->d_name);
				} else if (strncmp(":2,", colon, 3) == 0) {
					int alphabetic = 1;
					char last_flag = 0;
					for (const char* flag = colon + 3; *flag; ++flag) {
						if (*flag == ',') {
							/* dovecot extended for this, warn about it but don't error on it */
							printf("\n%s/%s: warning: , found in flags, indicative of Dovecot extensions.", subname, de->d_name);
							break;
						}

						/* TODO: Can we incorporate a check here for DUPLICATE flags */

						alphabetic &= *flag > last_flag;
						if (!strchr(valid_flags, *flag))
							add_error(ec, "%s/%s: invalid flag %c found.", subname, de->d_name, *flag);

						last_flag = *flag;
					}
					if (!alphabetic) {
						add_error(ec, "%s/%s: flags are not in alphabetic order.", subname, de->d_name);
						if (fix_fixable) {
							char t;
							char *fflag = (char*)colon + 3;
							char *oldname = strdup(de->d_name);
							for (char *tflag = fflag; *tflag && *tflag != ','; ++tflag) {
								t = *tflag;
								char *aflag = tflag;
								while (aflag > fflag && *(aflag-1) > t) {
									*aflag = *(aflag-1);
									aflag--;
								}
								*aflag = t;
							}

							/* reduce the risk of clobering a valid email file */
							if (fstatat(sfd, de->d_name, &st, AT_SYMLINK_NOFOLLOW) == 0 || errno != ENOENT) {
								/* just fail silently */
								strcpy(de->d_name, oldname);
							} else if (renameat(sfd, oldname, sfd, de->d_name) < 0) {
								printf("\nRename %s to %s failed: %s", oldname,
										de->d_name, strerror(errno));
								/* rename failed, so keep the old name for adding into mlist */
								strcpy(de->d_name, oldname);
							} else
								fixed++;
							free(oldname);
						}
					}

				} else {
					add_error(ec, "%s/%s: flags marker is not recognized, expected :2, - probably an unsupported version ...\n", subname, de->d_name);
				}

				/* only add here since alpha fix on flags can change de->d_name */
				msg_list_add(&mlist, subname, de->d_name);
			}
			closedir(dir);
		}
	}

	for (slist = mlist; slist; slist = slist->next) {
		/* Whilst base name has a structure, it really doesn't matter ...  the
		 * structure is merely intended to produce a unique - we NEED it to be
		 * unique, else the POP3 and IMAP servers tend to die. */

		/* We checked the filename structure above, so don't bother again,
		 * just check for duplicates here */
		if (slist->fullnames[1]) {
			// we know there is more than one, count them.
			int i;
			for (i = 1; slist->fullnames[i]; ++i)
				;
			add_error(ec, "%s: %d occurences, which means stuff is not unique.",
					slist->basename, i);
			for (i = 0; slist->fullnames[i]; ++i)
				printf("\n - %s", slist->fullnames[i]);
			fflush(stdout);

			if (fix_fixable) {
				const char* lkept = slist->fullnames[0];
				for (i = 1; slist->fullnames[i]; ++i) {
					if (copy_prefer_over(fd, lkept, slist->fullnames[i])) {
						if (unlinkat(fd, slist->fullnames[i], 0) < 0) {
							perror(slist->fullnames[i]);
						} else
							++fixed;
					} else if (copy_prefer_over(fd, slist->fullnames[i], lkept)) {
						if (unlinkat(fd, lkept, 0) < 0) {
							perror(lkept);
						} else
							++fixed;
						lkept = slist->fullnames[i];
					} else {
						printf("\nCannot choose between %s and %s.", lkept, slist->fullnames[i]);
						fflush(stdout);
					}
				}
			}
		}
	}

	if (ec) {
		printf("\n *** %d errors identified ***\n", ec);
	} else {
		printf(" All Good.\n");
	}

	//msg_list_dump(mlist);
	msg_list_free(mlist);

	return ec;
}

static
int check_path(const char* path)
{
	int ec, sfd;
	int fd = open(path, O_RDONLY);
	DIR* dir;
	struct dirent* de;
	struct stat st;
	uid_t uid;
	gid_t gid;

	if (fd < 0) {
		perror(path);
		return 1;
	}
	printf("PATH: %s\n", path);

	ec = myfstatat(fd, "", &st, AT_EMPTY_PATH);
	if (ec < 0) {
		printf("Error stat'ing base folder: %s.\n", strerror(errno));
		return 1;
	}

	uid = st.st_uid;
	gid = st.st_gid;

	ec = check_fdpath(fd, "", uid, gid);

	dir = fdopendir(fd);
	if (!dir) {
		printf("%s: %s\n", path, strerror(errno));
		close(fd);
		++ec;
	} else {
		while ((de = readdir(dir))) {
			if (de->d_name[0] != '.' || strcmp(de->d_name, "..") == 0 || strcmp(de->d_name, ".") == 0)
				continue;

			if (de->d_type == DT_UNKNOWN) {
				if (myfstatat(fd, de->d_name, &st, 0) < 0) {
					printf("%s/%s: %s.\n", path, de->d_name, strerror(errno));
					++ec;
					continue;
				}
				if (S_ISDIR(st.st_mode))
					de->d_type = DT_DIR;
			}

			if (de->d_type != DT_DIR) {
				printf("%s/%s: Not a folder (.Name entries must be folders).\n", path,
						de->d_name);
				++ec;
				continue;
			}

			sfd = openat(fd, de->d_name, O_RDONLY);
			if (sfd < 0) {
				printf("%s/%s: %s.\n", path, de->d_name, strerror(errno));
				continue;
			}
			ec += check_fdpath(sfd, de->d_name, uid, gid);
			close(sfd);
		}
		closedir(dir);
	}

	return ec;
}

static
void __attribute__((noreturn)) usage(int x)
{
	FILE *o = x ? stderr : stdout;

	fprintf(o, "USAGE: %s [options] folder [...]\n", progname);
	fprintf(o, "  -h|--help\n");
	fprintf(o, "    Display this text and terminate.\n");
	fprintf(o, "  -F,--fix-fixable\n");
	fprintf(o, "    Fix fixable errors, currently:\n");
	fprintf(o, "     - ownership of files.\n");
	fprintf(o, "Progam will exit with 0 exit code if, and only if none of the folders exhibit any errors:\n");
	fprintf(o, "  0 - no errors.\n");
	fprintf(o, "  1 - usage error (ie, we terminated due to a usage problem).\n");
	fprintf(o, "  2 - errors were encountered, see output from program for details.\n");
	fprintf(o, "  3 - errors were encountered, and possibly fixed.\n");
	fprintf(o, "WARNING:  This doesn't currently check anything server (courier/dovecot etc ...) specific.\n");
	fprintf(o, "SERIOUS WARNING: This uses stat ... a lot ... VERY slow on certain filesystems.\n");
	exit(x);
};

static struct option options[] = {
	{ "help",		no_argument, NULL, 'h' },
	{ "fix-fixable",no_argument, NULL, 'F' },
	{ NULL, 0, NULL, 0 }
};

int main(int argc, char **argv)
{
	progname = *argv;
	int c;

	while (( c = getopt_long(argc, argv, "hF", options, NULL)) != -1) {
		switch (c) {
		case 0:
			break;
		case 'h':
			usage(0);
		case 'F':
			fix_fixable = true;
			break;
		default:
			fprintf(stderr, "Option not implemented: %c.\n", c);
			usage(1);
		}
	}

	if (!argv[optind])
		usage(1);

	c = 0;
	while (argv[optind])
		c += check_path(argv[optind++]);
	return c ? (fixed ? 3 : 2) : 0;
}
