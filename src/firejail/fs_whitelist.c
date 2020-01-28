/*
 * Copyright (C) 2014-2019 Firejail Authors
 *
 * This file is part of firejail project
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License along
 * with this program; if not, write to the Free Software Foundation, Inc.,
 * 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA.
*/
#include "firejail.h"
#include <sys/mount.h>
#include <fnmatch.h>
#include <glob.h>
#include <errno.h>

#include <fcntl.h>
#ifndef O_PATH
# define O_PATH 010000000
#endif

#define MAXBUF 4096

// mountinfo functionality test;
// 1. enable TEST_MOUNTINFO definition
// 2. run firejail --whitelist=/any/directory
//#define TEST_MOUNTINFO

static int init_home = 0;

static char **whitelist = NULL;
static size_t whitelist_c = 0;
static size_t whitelist_m = 64;
static char **nowhitelist = NULL;
static size_t nowhitelist_c = 0;
static size_t nowhitelist_m = 32;
static char **topdirs = NULL;
static size_t topdirs_c = 0;
static size_t topdirs_m = 16;
typedef struct {
	char *src;
	char *dst;
} link_t;
static link_t *linklist = NULL;
static size_t linklist_c = 0;
static size_t linklist_m = 32;



static void whitelist_err(const char *path) {
	assert(path);
	fprintf(stderr, "Error: invalid whitelist path \"%s\"\n", path);
	exit(1);
}

// traverse path, create missing directories and return a
// a file descriptor for the last directory, or -1 if
// * something goes wrong
// * path element is a symlink (open fails with ENOTDIR)
// * a directory is a mount point
static int mkpath(const char *path) {
	assert(path && path[0] == '/');
	int created = 0;

	static char *runuser = NULL;
	static size_t runuser_len = 0;
	static size_t homedir_len = 0;
	if (!runuser) {
		if (asprintf(&runuser, "/run/user/%u", getuid()) == -1)
			errExit("asprintf");
		runuser_len = strlen(runuser);
		homedir_len = strlen(cfg.homedir);
	}

	// create directories with uid/gid as root, or as current user if inside home or run/user/$UID directory
	int userprivs = 0;
	if ((strncmp(path, cfg.homedir, homedir_len) == 0 && path[homedir_len] == '/') ||
	    (strncmp(path, runuser, runuser_len) == 0 && path[runuser_len] == '/')) {
		EUID_USER();
		userprivs = 1;
	}

	int fd = -1;
	int parentfd = open("/", O_PATH|O_DIRECTORY|O_CLOEXEC);
	if (parentfd == -1)
		errExit("open");

	// work with a copy of path
	char *dup = strdup(path);
	if (!dup)
		errExit("strdup");

	// don't create the last path element
	char *p = strrchr(dup+1, '/');
	assert(p);
	*p = '\0';

	char *tok = strtok(dup, "/");
	assert(tok);

	// initial dev number, it changes if we get to a mount point
	struct stat s;
	if (fstatat(parentfd, tok, &s, 0) == -1)
		errExit("fstatat");
	dev_t olddev = s.st_dev;

	while (tok) {
		// create the directory if necessary
		if (mkdirat(parentfd, tok, 0755) == -1) {
			if (errno != EEXIST) {
				if (arg_debug || arg_debug_whitelists)
					perror("mkdir");
				close(parentfd);
				free(dup);
				if (userprivs) {
					EUID_ROOT();
				}
				return -1;
			}
		}
		else
			created = 1;
		// open the directory
		fd = openat(parentfd, tok, O_PATH|O_DIRECTORY|O_NOFOLLOW|O_CLOEXEC);
		if (fd == -1) {
			if (arg_debug || arg_debug_whitelists)
				perror("open");
			close(parentfd);
			free(dup);
			if (userprivs) {
				EUID_ROOT();
			}
			return -1;
		}
		// check if directory is a mount point
		if (fstat(fd, &s) == -1)
			errExit("fstat");
		if (s.st_dev != olddev) {
			// found a mount point, we are done
			if (arg_debug || arg_debug_whitelists)
				printf("path is whitelisted already\n");
			close(parentfd);
			close(fd);
			free(dup);
			if (userprivs) {
				EUID_ROOT();
			}
			return -1;
		}
		// move on to next path segment
		close(parentfd);
		parentfd = fd;
		tok = strtok(NULL, "/");
	}

	if (created)
		fs_logger2("mkpath", path);

	free(dup);
	if (userprivs) {
		EUID_ROOT();
	}
	return fd;
}

static void whitelist_path(const char *dst) {
	EUID_ASSERT();
	assert(dst && dst[0] == '/');
	if (arg_debug || arg_debug_whitelists)
		printf("whitelisting %s\n", dst);

	// path of mount source
	char *src;
	if (asprintf(&src, "%s%s", RUN_WHITELIST_DIR, dst) == -1)
		errExit("asprintf");
	// open mount source, symbolic links are rejected
	int fd = safe_fd(src, O_PATH|O_NOFOLLOW|O_CLOEXEC);
	if (fd == -1) {
		if (arg_debug || arg_debug_whitelists) {
			perror("open");
			printf("Debug %d: skip whitelisting of %s\n", __LINE__, dst);
		}
		free(src);
		return;
	}
	struct stat s;
	if (fstat(fd, &s) == -1)
		errExit("fstat");
	if (S_ISLNK(s.st_mode)) {
		if (arg_debug || arg_debug_whitelists)
			printf("Debug %d: skip whitelisting of %s\n", __LINE__, dst);
		close(fd);
		free(src);
		return;
	}

	// create path of mount target and open the last directory in path,
	// don't follow symbolic links
	EUID_ROOT();
	int fd2 = mkpath(dst);
	EUID_USER();
	if (fd2 == -1) {
		if (arg_debug || arg_debug_whitelists)
			printf("Debug %d: skip whitelisting of %s\n", __LINE__, dst);
		close(fd);
		free(src);
		return;
	}
	// get file name of the mount target
	const char *file = gnu_basename(dst);
	// create and open the mount target itself, fails if there is a symbolic link in its place
	int fd3 = -1;
	if (S_ISDIR(s.st_mode)) {
		EUID_ROOT();
		int rv = mkdirat(fd2, file, 0755);
		EUID_USER();
		// directory can exist already:
		// firejail --whitelist=/foo/bar --whitelist=/foo/bar
		// or
		// firejail --whitelist=/foo/bar --whitelist=/foo
		// (firejail --whitelist=/foo --whitelist=/foo/bar is filtered out by mkpath)
		if (rv == -1 && errno != EEXIST) {
			if (arg_debug || arg_debug_whitelists) {
				perror("mkdir");
				printf("Debug %d: skip whitelisting of %s\n", __LINE__, dst);
			}
			close(fd);
			close(fd2);
			free(src);
			return;
		}
		fd3 = openat(fd2, file, O_PATH|O_DIRECTORY|O_NOFOLLOW|O_CLOEXEC);
	}
	else {
		// an existing non-directory mount target indicates an earlier whitelist mount:
		// firejail --whitelist=/foo/bar --whitelist=/foo/bar
		// (firejail --whitelist=/foo --whitelist=/foo/bar is filtered out by mkpath)
		// open will fail in this case (O_EXCL)
		EUID_ROOT();
		fd3 = openat(fd2, file, O_RDONLY|O_CREAT|O_EXCL|O_CLOEXEC, S_IRUSR|S_IWUSR);
		EUID_USER();
	}
	close(fd2);

	if (fd3 == -1) {
		if (arg_debug || arg_debug_whitelists) {
			perror("open");
			printf("Debug %d: skip whitelisting of %s\n", __LINE__, dst);
		}
		close(fd);
		free(src);
		return;
	}

	// path of both mount source and mount target was traversed and
	// no symbolic link was found; mount via magic links in /proc/self/fd
	// in order to make this mount resilient against symlink attacks
	char *proc_src, *proc_dst;
	if (asprintf(&proc_src, "/proc/self/fd/%d", fd) == -1)
		errExit("asprintf");
	if (asprintf(&proc_dst, "/proc/self/fd/%d", fd3) == -1)
		errExit("asprintf");
	EUID_ROOT();
	if (mount(proc_src, proc_dst, NULL, MS_BIND|MS_REC, NULL) < 0)
		errExit("mount bind");
	EUID_USER();
	// check the last mount operation
	MountData *mptr = get_last_mount(); // will do exit(1) if the mount cannot be found
#ifdef TEST_MOUNTINFO
	printf("mountinfo functionality test\n");
	mptr->dir = "foo";
#endif
	// confirm the file was mounted on the right target
	// strcmp does not work here, because mptr->dir can be a submount
	size_t dst_len = strlen(dst);
	if (strncmp(mptr->dir, dst, dst_len) != 0 ||
	   (*(mptr->dir + dst_len) != '\0' && *(mptr->dir + dst_len) != '/'))
		errLogExit("invalid whitelist mount");
	fs_logger2("whitelist", dst);
	free(proc_src);
	free(proc_dst);
	free(src);
	close(fd);
	close(fd3);
}

static int nowhitelist_match(const char *path) {
	assert(path);
	size_t i;
	for (i = 0; i < nowhitelist_c; i++) {
		int result = fnmatch(nowhitelist[i], path, FNM_PATHNAME);
		if (result == FNM_NOMATCH)
			continue;
		else if (result == 0) {
			if (arg_debug || arg_debug_whitelists) {
				printf("Removed whitelist path: %s\n", path);
				printf("\tnowhitelisted\n");
			}
			return 1;
		}
		else {
			fprintf(stderr, "Error: failed to compare path %s with pattern %s\n", path, nowhitelist[i]);
			exit(1);
		}
	}
	return 0;
}

static void init_tmpfs(const char *dir, int fd) {
	assert(dir);
	size_t len = strlen(dir);
	// create empty user-owned /tmp/user/$UID directory (pam-tmpdir)
	if (strcmp(dir, "/tmp") == 0) {
		char *env = getenv("TMP");
		if (env) {
			char *pamtmpdir;
			if (asprintf(&pamtmpdir, "/tmp/user/%u", getuid()) == -1)
				errExit("asprintf");
			if (strcmp(env, pamtmpdir) == 0) {
				mkdir_attr("/tmp/user", 0711, 0, 0);
				fs_logger2("mkdir", "/tmp/user");
				mkdir_attr(pamtmpdir, 0700, getuid(), 0);
				fs_logger2("mkdir", pamtmpdir);
			}
			free(pamtmpdir);
		}
	}
	// create empty user-owned /run/user/$UID directory
	// whitelist /run/firejail directory using a file descriptor
	else if (strcmp(dir, "/run") == 0) {
		mkdir_attr("/run/user", 0755, 0, 0);
		fs_logger2("mkdir", "/run/user");
		char *runuser;
		if (asprintf(&runuser, "/run/user/%u", getuid()) == -1)
			errExit("asprintf");
		mkdir_attr(runuser, 0700, getuid(), getgid());
		fs_logger2("mkdir", runuser);
		free(runuser);

		mkdir_attr(RUN_FIREJAIL_DIR, 0755, 0, 0);
		char *proc;
		if (asprintf(&proc, "/proc/self/fd/%d", fd) == -1)
			errExit("asprintf");
		if (mount(proc, RUN_FIREJAIL_DIR, NULL, MS_BIND|MS_REC, NULL) < 0)
			errExit("mount bind");
		free(proc);
		fs_logger2("whitelist", RUN_FIREJAIL_DIR);
	}

	// create empty home directory
	if (strncmp(dir, cfg.homedir, len) == 0) {
		if (cfg.homedir[len] == '/') {
			assert(init_home == 0);
			// open home directory
			char *newname;
			if (asprintf(&newname, "%s%s", RUN_WHITELIST_DIR, cfg.homedir) == -1)
				errExit("asprintf");
			int fd = safe_fd(newname, O_PATH|O_DIRECTORY|O_NOFOLLOW|O_CLOEXEC);
			free(newname);
			if (fd == -1) {
				if (errno == ENOENT) // nothing to do if home directory does not exist
					return;
				fprintf(stderr, "Error: cannot open home directory\n");
				exit(1);
			}
			// read directory ownership and permissions
			struct stat s;
			if (fstat(fd, &s) == -1)
				errExit("fstat");
			close(fd);

			// create a new home directory
			assert(strncmp(cfg.homedir, RUN_FIREJAIL_DIR, strlen(RUN_FIREJAIL_DIR)) != 0 ||
			      (cfg.homedir[strlen(RUN_FIREJAIL_DIR)] != '/' && cfg.homedir[strlen(RUN_FIREJAIL_DIR)] != '\0'));
			int rv = mkdir(cfg.homedir, 0700);
			if (rv == -1) {
				if (mkpath_as_root(cfg.homedir) == -1)
					errExit("mkpath");
				if ((rv = mkdir(cfg.homedir, 0700)) == -1 && errno != EEXIST)
					errExit("mkdir");
			}
			// set ownership and permissions
			if (rv == 0 && set_perms(cfg.homedir, s.st_uid, s.st_gid, s.st_mode & 07777))
				errExit("chmod/chown");
		}
		else if (cfg.homedir[len] != '\0')
			return;

		init_home = 1;
	}
}

static void mount_tmpfs(const char *dir) {
	assert(dir);
	int fd = -1;

	struct stat s;
	if (lstat(dir, &s) == 0) {
		if (S_ISDIR(s.st_mode)) {
			// keep a copy of dir in RUN_WHITELIST_DIR (/run/firejail/mnt/whitelist/dir)
			char *dest;
			if (asprintf(&dest, "%s%s", RUN_WHITELIST_DIR, dir) == -1)
				errExit("asprintf");
			if (arg_debug || arg_debug_whitelists)
				fprintf(stderr, "Mounting %s on %s\n", dir, dest);
			if (mkdir(dest, 0755) == -1)
				errExit("mkdir");
			if (mount(dir, dest, NULL, MS_BIND|MS_REC, NULL) < 0)
				errExit("mount bind");

			// open /run/firejail, so we can bring back the directory after a tmpfs is mounted on /run
			if (strcmp(dir, "/run") == 0) {
				fd = safe_fd(RUN_FIREJAIL_DIR, O_PATH|O_DIRECTORY|O_NOFOLLOW|O_CLOEXEC);
				if (fd == -1)
					errExit("opening " RUN_FIREJAIL_DIR);
			}

			// mount a tmpfs on dir
			if (arg_debug_whitelists && !arg_debug) // fs_tmpfs() prints a debug message itself
				printf("Mounting tmpfs on %s\n", dir);
			fs_tmpfs(dir, 0);
			init_tmpfs(dir, fd);

			free(dest);
			if (fd != -1)
				close(fd);
		}
		// if dir is a symbolic link, firejail does nothing but printing messages
		// (paths are not added to the whitelist array, and mkpath always fails with -1)
		else if (S_ISLNK(s.st_mode))
			fwarning("not mounting tmpfs on %s: is a symbolic link\n", dir);
		// for example something like --whitelist=/regularfile/doesntexist
		else
			fwarning("cannot mount tmpfs on %s: not a directory\n", dir);
	}
}

// exit if the top level directory is not allowed
// todo: expose this in firejail configuration file
static void check_topdir(const char *path) {
	assert(path);
	static char *deny_whitelist[] = {"/", "/proc", "/sys", NULL};

	size_t i;
	for (i = 0; deny_whitelist[i]; i++) {
		if (strcmp(path, deny_whitelist[i]) == 0) {
			fprintf(stderr, "Error: invalid whitelist top level directory \"%s\"\n", path);
			exit(1);
		}
	}
}

static size_t store_topdir(const char *path) {
	assert(path);
	char *dup = strdup(path);
	if (!dup)
		errExit("strdup");

	// identify the top level directory
	// note: this function is called also when there are unresolved macros,
	// so it is possible that path/dup is a top level directory already
	assert(dup[0] == '/');
	char *p = strchr(dup+1, '/');
	if (p)
		*p = '\0';

	// return length of top level directory string
	size_t rv = strlen(dup);

	// is top level directory in topdirs array?
	size_t i;
	for (i = 0; i < topdirs_c; i++) {
		if (strcmp(dup, topdirs[i]) == 0) {
			free(dup);
			return rv;
		}
	}
	// some top level directories are not allowed
	check_topdir(dup);
	// add top level directory to topdirs array
	topdirs[topdirs_c] = dup;
	if (++topdirs_c >= topdirs_m) {
		topdirs_m *= 2;
		topdirs = realloc(topdirs, sizeof(*topdirs) * topdirs_m);
		if (!topdirs)
			errExit("realloc");
	}
	return rv;
}

static void store_whitelist(const char *path) {
	assert(path);
	char *dup = strdup(path);
	if (!dup)
		errExit("strdup");
	whitelist[whitelist_c] = dup;
	if (++whitelist_c >= whitelist_m) {
		whitelist_m *= 2;
		whitelist = realloc(whitelist, sizeof(*whitelist) * whitelist_m);
		if (!whitelist)
			errExit("realloc");
	}
}

static void create_symlink(link_t link) {
	assert(link.src && link.dst);
	struct stat s;

	if (lstat(link.src, &s) == -1) {
		if (arg_debug || arg_debug_whitelists)
			printf("Creating symbolic link %s\n", link.src);
		int fd = mkpath(link.src);
		if (fd == -1) {
			if (arg_debug || arg_debug_whitelists)
				printf("Debug %d: cannot create symbolic link %s\n", __LINE__, link.src);
			return;
		}
		const char *base = gnu_basename(link.src);
		if (symlinkat(link.dst, fd, base) == -1) {
			if (arg_debug || arg_debug_whitelists) {
				perror("symlink");
				printf("Debug %d: cannot create symbolic link %s\n", __LINE__, link.src);
			}
		}
	}
}

static void store_symlink(const char *path) {
	assert(path && path[0] == '/');
	char buf[MAXBUF];

	ssize_t rv = readlink(path, buf, MAXBUF - 1);
	if (rv > 0) {
		// don't accept truncated return value
		if (rv == MAXBUF - 1) {
			fprintf(stderr, "Error: cannot read symbolic link %s\n", path);
			exit(1);
		}
		buf[rv] = '\0';
		// store link in linklist array
		char *name = strdup(path);
		if (!name)
			errExit("strdup");
		char *value = strdup(buf);
		if (!value)
			errExit("strdup");
		linklist[linklist_c].src = name;
		linklist[linklist_c].dst = value;
		if (++linklist_c >= linklist_m) {
			linklist_m *= 2;
			linklist = realloc(linklist, sizeof(*linklist) * linklist_m);
			if (!linklist)
				errExit("realloc");
		}
	}
}

void fs_whitelist(void) {
	ProfileEntry *entry = cfg.profile;
	if (!entry)
		return;

	EUID_USER();
	// allocate memory for nowhitelist
	nowhitelist = calloc(nowhitelist_m, sizeof(*nowhitelist));
	if (!nowhitelist)
		errExit("calloc");

	int globflags = GLOB_PERIOD | GLOB_NOSORT | GLOB_NOCHECK;
	glob_t globbuf;
	memset(&globbuf, 0, sizeof(globbuf));

	// expand macros, fill nowhitelist array and glob array
	while (entry) {
		int nowhitelist_flag = 0;

		// handle only whitelist and nowhitelist commands
		if (strncmp(entry->data, "whitelist ", 10) == 0)
			nowhitelist_flag = 0;
		else if (strncmp(entry->data, "nowhitelist ", 12) == 0)
			nowhitelist_flag = 1;
		else {
			entry = entry->next;
			continue;
		}
		char *dataptr = (nowhitelist_flag)? entry->data + 12: entry->data + 10;
		if (*dataptr == '\0')
			whitelist_err(dataptr);

		// replace ~/ into /home/username or try to resolve macro
		char *pattern = expand_macros(dataptr);
		assert(pattern);

		if (arg_debug || arg_debug_whitelists)
			printf("%s pattern: %s\n", (nowhitelist_flag)? "nowhitelist": "whitelist", pattern);

		// store pattern in nowhitelist array
		if (nowhitelist_flag) {
			nowhitelist[nowhitelist_c] = pattern;
			if (++nowhitelist_c >= nowhitelist_m) {
				nowhitelist_m *= 2;
				nowhitelist = realloc(nowhitelist, sizeof(*nowhitelist) * nowhitelist_m);
				if (!nowhitelist)
					errExit("realloc");
			}
			entry = entry->next;
			continue;
		}

		// whitelist globbing
		EUID_ASSERT();
		if (glob(pattern, globflags, NULL, &globbuf) != 0) {
			fprintf(stderr, "Error: failed to glob pattern %s\n", pattern);
			exit(1);
		}
		globflags |= GLOB_APPEND;
		entry = entry->next;
		free(pattern);
	}

	// return if there are no whitelist commands
	if ((globflags & GLOB_APPEND) == 0) {
		size_t i;
		for (i = 0; i < nowhitelist_c; i++)
			free(nowhitelist[i]);
		free(nowhitelist);
		EUID_ROOT();
		return;
	}

	// allocate memory
	topdirs = calloc(topdirs_m, sizeof(*topdirs));
	if (!topdirs)
		errExit("calloc");
	whitelist = calloc(whitelist_m, sizeof(*whitelist));
	if (!whitelist)
		errExit("calloc");
	linklist = calloc(linklist_m, sizeof(*linklist));
	if (!linklist)
		errExit("calloc");

	size_t i;
	for (i = 0; i < globbuf.gl_pathc; i++) {
		assert(globbuf.gl_pathv[i]);
		if (arg_debug || arg_debug_whitelists)
			printf("expanded whitelist pattern: %s\n", globbuf.gl_pathv[i]);

		// /home/me/.* can glob to /home/me/.. which would resolve to /home/
		const char *base = gnu_basename(globbuf.gl_pathv[i]);
		if (strcmp(base, ".") == 0 || strcmp(base, "..") == 0)
			continue;
		// filter nowhitelisted entries
		if (nowhitelist_match(globbuf.gl_pathv[i]))
			continue;

		if (globbuf.gl_pathv[i][0] != '/') { // absolute path?
			if (macro_id(globbuf.gl_pathv[i]) != -1) { // got a valid but unresolved macro
				struct stat s;
				if (!arg_quiet && stat(cfg.homedir, &s) == 0) {
					fprintf(stderr, "***\n");
					fprintf(stderr, "*** Warning: cannot whitelist %s directory\n", globbuf.gl_pathv[i]);
					fprintf(stderr, "*** Any file saved in this directory will be lost when the sandbox is closed.\n");
					fprintf(stderr, "***\n");
				}
				store_topdir(cfg.homedir); // mount a tmpfs on top level directory of homedir
				continue;
			}
			whitelist_err(globbuf.gl_pathv[i]);
		}

		// remove consecutive slashes, trailing slash and single dots
		char *path = clean_pathname(globbuf.gl_pathv[i]);

		// path should not be a top level directory or the root directory
		assert(path && path[0] == '/' && !strstr(path, ".."));
		if (!strchr(path+1, '/'))
			whitelist_err(path);

		// identify the top level directory, run some checks against the string
		// and store it in an array; returns length of top level directory string
		size_t len = store_topdir(path);

		// resolve path and add it to the whitelist array ...
		EUID_ASSERT();
		char *rp = realpath(path, NULL);
		if (rp) {
			// ... but only if it is not in /run/firejail
			if (strncmp(rp, RUN_FIREJAIL_DIR, strlen(RUN_FIREJAIL_DIR)) == 0 &&
			   (rp[strlen(RUN_FIREJAIL_DIR)] == '/' || rp[strlen(RUN_FIREJAIL_DIR)] == '\0'))
				whitelist_err(path);
			// ... and only if resolved path and unresolved path share the same top level directory
			if (strncmp(rp, path, len) == 0 && rp[len] == '/')
				store_whitelist(rp);
			// if unresolved path is a symbolic link, add it to the linklist array
			if (strcmp(rp, path) != 0)
				store_symlink(path);
		}
		else if (arg_debug || arg_debug_whitelists) {
			printf("Removed whitelist path: %s\n", path);
			printf("\treal path: (null)\n");
			printf("\t");fflush(0);
			perror("realpath");
		}

		free(path);
		free(rp);
	}
	globfree(&globbuf);

	// keep a copy of ~/.asoundrc and ~/.Xauthority
	EUID_ROOT();
	int aflag = store_asoundrc();
	int xflag = store_xauthority();

	// mount tmpfs on top directories
	mkdir_attr(RUN_WHITELIST_DIR, 0755, 0, 0);
	for (i = 0; i < topdirs_c; i++) {
		mount_tmpfs(topdirs[i]);
		free(topdirs[i]);
	}
	free(topdirs);

	// more home directory initialization: ~/.asoundrc and ~/.Xauthority
	if (init_home) {
		if (xflag)
			copy_xauthority();
		if (aflag)
			copy_asoundrc();
	}
	else { // cleanup
		unlink(RUN_ASOUNDRC_FILE);
		unlink(RUN_XAUTHORITY_FILE);
	}

	// do the whitelisting
	EUID_USER();
	for (i = 0; i < whitelist_c; i++) {
		whitelist_path(whitelist[i]);
		free(whitelist[i]);
	}
	free(whitelist);

	// finish initialization of home directory (~/.bashrc)
	// does nothing if file is whitelisted already
	EUID_ROOT();
	if (init_home)
		skel(cfg.homedir, getuid(), getgid());

	// create symbolic links
	for (i = 0; i < linklist_c; i++) {
		create_symlink(linklist[i]);
		free(linklist[i].src);
		free(linklist[i].dst);
	}
	free(linklist);

	// release nowhitelist memory
	for (i = 0; i < nowhitelist_c; i++)
		free(nowhitelist[i]);
	free(nowhitelist);

	// mask RUN_WHITELIST_DIR
	if (mount("tmpfs", RUN_WHITELIST_DIR, "tmpfs", MS_NOSUID | MS_STRICTATIME,  "mode=755,gid=0") < 0)
		errExit("masking " RUN_WHITELIST_DIR);
	fs_logger2("tmpfs", RUN_WHITELIST_DIR);
}
