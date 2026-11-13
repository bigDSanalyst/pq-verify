/*
 * pqv_worker -- the contained worker behind `pq-verify --audit-contained`.
 *
 * A Crucible-protocol harness (JSON lines on stdin and stdout; see
 * pq_verify/harness_audit.py) for an ML-KEM shared library with the
 * derandomised NIST API:
 *
 *     int keypair_derand(uint8_t *ek, uint8_t *dk, const uint8_t *coins);
 *     int enc_derand(uint8_t *ct, uint8_t *ss, const uint8_t *ek, const uint8_t *m);
 *     int dec(uint8_t *ss, const uint8_t *ct, const uint8_t *dk);
 *
 * coins is d || z (64 bytes). A nonzero return is a refusal.
 *
 * pq-verify starts the worker with the library as an inherited, sealed memfd.
 * The worker is sent inputs, calls the library and returns what the library
 * wrote. It is never sent an expected answer: scoring happens in pq-verify's
 * own process.
 *
 * Order of events. pq-verify checks steps 1 and 2 from outside, in
 * /proc/<pid>/status and /proc/<pid>/maps, before it lets step 5 happen:
 *
 *   1. no core dumps, no_new_privs, every capability dropped;
 *   2. the seccomp filter below is installed;
 *   3. the worker does, under the filter, what it and the dynamic loader will
 *      need to do later (allocate, read a file, list a directory, start a
 *      thread). If the filter stops this system's own C library, the worker
 *      dies here, before any vendor code is mapped, and that is reported as
 *      a fault of the audit and not of the library;
 *   4. it prints {"stage": "contained"} and waits for {"load": true};
 *   5. dlopen("/proc/self/fd/N"): the library's constructors, like everything
 *      after them, run under the filter;
 *   6. the handshake, then one reply per request.
 *
 * The filter is a deny-list (SECCOMP_RET_KILL_PROCESS). On it: starting a
 * process, exec, a new session or process group; sockets; opening a file for
 * writing, creating, renaming, removing or truncating one, changing its mode,
 * owner, times or attributes; signals to, and tracing or reading of, other
 * processes; io_uring; mounts and namespaces; keyrings, System V IPC and
 * POSIX message queues. `pqv_worker --policy` prints it. Everything else is
 * allowed, reading any file the user can read included. It is not a sandbox.
 */
#define _GNU_SOURCE
#include <dirent.h>
#include <dlfcn.h>
#include <errno.h>
#include <fcntl.h>
#include <linux/audit.h>
#include <linux/capability.h>
#include <linux/filter.h>
#include <linux/seccomp.h>
#include <pthread.h>
#include <signal.h>
#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/prctl.h>
#include <sys/resource.h>
#include <sys/syscall.h>
#include <sys/types.h>
#include <time.h>
#include <unistd.h>

#define PQV_WORKER_VERSION "1"

#if defined(__x86_64__)
#define PQV_ARCH AUDIT_ARCH_X86_64
#elif defined(__aarch64__)
#define PQV_ARCH AUDIT_ARCH_AARCH64
#else
#error "the contained worker is written for x86-64 and AArch64 Linux"
#endif
/* pq-verify starts it on x86-64 only (pq_verify/contained.py): the AArch64
   branches here have been compiled by nobody and run by nothing. */
#if !defined(__BYTE_ORDER__) || __BYTE_ORDER__ != __ORDER_LITTLE_ENDIAN__
#error "the contained worker reads the low half of a syscall argument: little-endian only"
#endif

#ifndef SECCOMP_RET_KILL_PROCESS
#define SECCOMP_RET_KILL_PROCESS 0x80000000U
#endif
#ifndef PR_SET_NO_NEW_PRIVS
#define PR_SET_NO_NEW_PRIVS 38
#endif
#ifndef PR_CAPBSET_DROP
#define PR_CAPBSET_DROP 24
#endif
#ifndef CLONE_THREAD
#define CLONE_THREAD 0x00010000
#endif

/* The O_TMPFILE bit alone. glibc's __O_TMPFILE is this bit OR O_DIRECTORY,
   and a mask holding O_DIRECTORY would stop a library that only lists a
   directory. */
#define PQV_O_TMPFILE_BIT 020000000u
#define PQV_WRITE_FLAGS \
    ((uint32_t)(O_WRONLY | O_RDWR | O_CREAT | O_TRUNC | O_APPEND) | PQV_O_TMPFILE_BIT)

/* ioctl requests that change something through a descriptor opened for
   reading: input pushed into a terminal, and inode flags. */
#define PQV_TIOCSTI          0x5412u
#define PQV_TIOCLINUX        0x541Cu
#define PQV_FS_IOC_SETFLAGS  0x40086602u
#define PQV_FS_IOC32_SETFLAGS 0x40046602u
#define PQV_FS_IOC_FSSETXATTR 0x401c5820u

/* System calls newer than some C libraries' headers. From 424 on the numbers
   are the same on every architecture. */
#ifndef SYS_pidfd_send_signal
#define SYS_pidfd_send_signal 424
#endif
#ifndef SYS_io_uring_setup
#define SYS_io_uring_setup 425
#endif
#ifndef SYS_io_uring_enter
#define SYS_io_uring_enter 426
#endif
#ifndef SYS_io_uring_register
#define SYS_io_uring_register 427
#endif
#ifndef SYS_open_tree
#define SYS_open_tree 428
#endif
#ifndef SYS_move_mount
#define SYS_move_mount 429
#endif
#ifndef SYS_fsopen
#define SYS_fsopen 430
#endif
#ifndef SYS_fsconfig
#define SYS_fsconfig 431
#endif
#ifndef SYS_fsmount
#define SYS_fsmount 432
#endif
#ifndef SYS_fspick
#define SYS_fspick 433
#endif
#ifndef SYS_pidfd_open
#define SYS_pidfd_open 434
#endif
#ifndef SYS_clone3
#define SYS_clone3 435
#endif
#ifndef SYS_openat2
#define SYS_openat2 437
#endif
#ifndef SYS_pidfd_getfd
#define SYS_pidfd_getfd 438
#endif
#ifndef SYS_process_madvise
#define SYS_process_madvise 440
#endif
#ifndef SYS_mount_setattr
#define SYS_mount_setattr 442
#endif
#ifndef SYS_process_mrelease
#define SYS_process_mrelease 448
#endif
#ifndef SYS_fchmodat2
#define SYS_fchmodat2 452
#endif
#ifndef SYS_setxattrat
#define SYS_setxattrat 463
#endif
#ifndef SYS_removexattrat
#define SYS_removexattrat 466
#endif
#ifndef SYS_open_tree_attr
#define SYS_open_tree_attr 467
#endif
#ifndef SYS_file_setattr
#define SYS_file_setattr 469
#endif

struct denied { const char *name; long nr; };

/* Refused whatever the arguments. */
static const struct denied k_deny[] = {
    /* a new process, another program, a session or group of its own */
#ifdef SYS_fork
    { "fork", SYS_fork },
#endif
#ifdef SYS_vfork
    { "vfork", SYS_vfork },
#endif
    { "execve", SYS_execve },
    { "execveat", SYS_execveat },
    { "setsid", SYS_setsid },
    { "setpgid", SYS_setpgid },
    /* the network */
    { "socket", SYS_socket },
    { "socketpair", SYS_socketpair },
    { "connect", SYS_connect },
    { "bind", SYS_bind },
    { "listen", SYS_listen },
    { "accept", SYS_accept },
    { "accept4", SYS_accept4 },
    /* other processes: tracing them, reading or writing their memory,
       descriptors for them */
    { "ptrace", SYS_ptrace },
    { "process_vm_readv", SYS_process_vm_readv },
    { "process_vm_writev", SYS_process_vm_writev },
    { "pidfd_open", SYS_pidfd_open },
    { "pidfd_getfd", SYS_pidfd_getfd },
    { "pidfd_send_signal", SYS_pidfd_send_signal },
    { "process_madvise", SYS_process_madvise },
    { "process_mrelease", SYS_process_mrelease },
    { "perf_event_open", SYS_perf_event_open },
    /* io_uring does opens, writes and connects of its own, which a filter on
       system calls does not see */
    { "io_uring_setup", SYS_io_uring_setup },
    { "io_uring_enter", SYS_io_uring_enter },
    { "io_uring_register", SYS_io_uring_register },
    /* files: creating, renaming, linking, removing. openat2 takes its flags
       in memory, where a filter cannot read them, so it is refused whole. */
    { "openat2", SYS_openat2 },
#ifdef SYS_creat
    { "creat", SYS_creat },
#endif
#ifdef SYS_rename
    { "rename", SYS_rename },
#endif
    { "renameat", SYS_renameat },
    { "renameat2", SYS_renameat2 },
#ifdef SYS_unlink
    { "unlink", SYS_unlink },
#endif
    { "unlinkat", SYS_unlinkat },
#ifdef SYS_link
    { "link", SYS_link },
#endif
    { "linkat", SYS_linkat },
#ifdef SYS_symlink
    { "symlink", SYS_symlink },
#endif
    { "symlinkat", SYS_symlinkat },
#ifdef SYS_mkdir
    { "mkdir", SYS_mkdir },
#endif
    { "mkdirat", SYS_mkdirat },
#ifdef SYS_rmdir
    { "rmdir", SYS_rmdir },
#endif
#ifdef SYS_mknod
    { "mknod", SYS_mknod },
#endif
    { "mknodat", SYS_mknodat },
    /* files: their length */
    { "truncate", SYS_truncate },
    { "ftruncate", SYS_ftruncate },
    { "fallocate", SYS_fallocate },
    /* files: mode, owner, times, attributes. Several of these work on a
       descriptor opened for reading. */
#ifdef SYS_chmod
    { "chmod", SYS_chmod },
#endif
    { "fchmod", SYS_fchmod },
    { "fchmodat", SYS_fchmodat },
    { "fchmodat2", SYS_fchmodat2 },
#ifdef SYS_chown
    { "chown", SYS_chown },
#endif
#ifdef SYS_lchown
    { "lchown", SYS_lchown },
#endif
    { "fchown", SYS_fchown },
    { "fchownat", SYS_fchownat },
#ifdef SYS_utime
    { "utime", SYS_utime },
#endif
#ifdef SYS_utimes
    { "utimes", SYS_utimes },
#endif
#ifdef SYS_futimesat
    { "futimesat", SYS_futimesat },
#endif
    { "utimensat", SYS_utimensat },
    { "setxattr", SYS_setxattr },
    { "lsetxattr", SYS_lsetxattr },
    { "fsetxattr", SYS_fsetxattr },
    { "setxattrat", SYS_setxattrat },
    { "removexattr", SYS_removexattr },
    { "lremovexattr", SYS_lremovexattr },
    { "fremovexattr", SYS_fremovexattr },
    { "removexattrat", SYS_removexattrat },
    { "file_setattr", SYS_file_setattr },
    /* mounts and namespaces */
    { "mount", SYS_mount },
    { "umount2", SYS_umount2 },
    { "unshare", SYS_unshare },
    { "setns", SYS_setns },
    { "chroot", SYS_chroot },
    { "pivot_root", SYS_pivot_root },
    { "open_tree", SYS_open_tree },
    { "open_tree_attr", SYS_open_tree_attr },
    { "move_mount", SYS_move_mount },
    { "fsopen", SYS_fsopen },
    { "fsconfig", SYS_fsconfig },
    { "fsmount", SYS_fsmount },
    { "fspick", SYS_fspick },
    { "mount_setattr", SYS_mount_setattr },
    /* keyrings, System V IPC, POSIX message queues: state shared with other
       processes that is not a file */
    { "add_key", SYS_add_key },
    { "request_key", SYS_request_key },
    { "keyctl", SYS_keyctl },
    { "shmget", SYS_shmget },
    { "shmat", SYS_shmat },
    { "shmctl", SYS_shmctl },
    { "semget", SYS_semget },
    { "semop", SYS_semop },
    { "semtimedop", SYS_semtimedop },
    { "semctl", SYS_semctl },
    { "msgget", SYS_msgget },
    { "msgsnd", SYS_msgsnd },
    { "msgrcv", SYS_msgrcv },
    { "msgctl", SYS_msgctl },
    { "mq_open", SYS_mq_open },
    { "mq_unlink", SYS_mq_unlink },
    { "mq_timedsend", SYS_mq_timedsend },
    { "mq_timedreceive", SYS_mq_timedreceive },
    { "mq_notify", SYS_mq_notify },
    { "mq_getsetattr", SYS_mq_getsetattr },
    /* kernel facilities a library under audit has no use for */
    { "bpf", SYS_bpf },
    { "userfaultfd", SYS_userfaultfd },
};
#define N_DENY (sizeof k_deny / sizeof k_deny[0])

/* Refused for some arguments: the system calls, then what --policy says of
   them. */
static const struct denied k_conditional[] = {
    { "clone", SYS_clone },
    { "clone3", SYS_clone3 },
    { "openat", SYS_openat },
#ifdef SYS_open
    { "open", SYS_open },
#endif
    { "kill", SYS_kill },
    { "tgkill", SYS_tgkill },
    { "tkill", SYS_tkill },
    { "rt_sigqueueinfo", SYS_rt_sigqueueinfo },
    { "rt_tgsigqueueinfo", SYS_rt_tgsigqueueinfo },
    { "prlimit64", SYS_prlimit64 },
    { "ioctl", SYS_ioctl },
};

static const char *const k_rules[] = {
    "clone        unless CLONE_THREAD is set (a thread, not a process)",
    "clone3       answered ENOSYS, so the C library falls back to clone",
    "openat       with O_WRONLY, O_RDWR, O_CREAT, O_TRUNC, O_APPEND or O_TMPFILE",
#ifdef SYS_open
    "open         with O_WRONLY, O_RDWR, O_CREAT, O_TRUNC, O_APPEND or O_TMPFILE",
#endif
    "kill         unless the target is the worker itself",
    "tgkill       unless the target is the worker itself",
    "tkill        unless the target is the worker's first thread",
    "rt_sigqueueinfo, rt_tgsigqueueinfo  unless the target is the worker itself",
    "prlimit64    unless the target is the worker itself",
    "ioctl        TIOCSTI, TIOCLINUX, FS_IOC_SETFLAGS, FS_IOC_FSSETXATTR",
    "every system call of another ABI (32-bit, x32)",
};

/* ------------------------------------------------------------------ */
/* the filter                                                         */
/* ------------------------------------------------------------------ */

#define MAX_FILTER 1024
static struct sock_filter g_prog[MAX_FILTER];
static unsigned g_n;
static int g_overflow;

static void emit(uint16_t code, uint8_t jt, uint8_t jf, uint32_t k)
{
    if (g_n >= MAX_FILTER) { g_overflow = 1; return; }
    g_prog[g_n].code = code; g_prog[g_n].jt = jt; g_prog[g_n].jf = jf; g_prog[g_n].k = k;
    g_n++;
}

static void load_nr(void)
{
    emit(BPF_LD | BPF_W | BPF_ABS, 0, 0, (uint32_t)offsetof(struct seccomp_data, nr));
}

static void load_arg(unsigned idx)     /* its low 32 bits */
{
    emit(BPF_LD | BPF_W | BPF_ABS, 0, 0,
         (uint32_t)(offsetof(struct seccomp_data, args) + 8u * idx));
}

static void ret_kill(void) { emit(BPF_RET | BPF_K, 0, 0, SECCOMP_RET_KILL_PROCESS); }

/* Each rule begins and ends with the system call number loaded. */

static void deny(long nr)
{
    emit(BPF_JMP | BPF_JEQ | BPF_K, 0, 1, (uint32_t)nr);
    ret_kill();
}

/* nr, and (argument & mask) is nonzero (kill_if_set) or zero: kill */
static void deny_bits(long nr, unsigned idx, uint32_t mask, int kill_if_set)
{
    emit(BPF_JMP | BPF_JEQ | BPF_K, 0, 4, (uint32_t)nr);
    load_arg(idx);
    emit(BPF_JMP | BPF_JSET | BPF_K, kill_if_set ? 0 : 1, kill_if_set ? 1 : 0, mask);
    ret_kill();
    load_nr();
}

/* nr, and argument == value: kill */
static void deny_value(long nr, unsigned idx, uint32_t value)
{
    emit(BPF_JMP | BPF_JEQ | BPF_K, 0, 4, (uint32_t)nr);
    load_arg(idx);
    emit(BPF_JMP | BPF_JEQ | BPF_K, 0, 1, value);
    ret_kill();
    load_nr();
}

/* nr, and argument is neither a nor b: kill */
static void allow_only(long nr, unsigned idx, uint32_t a, uint32_t b)
{
    emit(BPF_JMP | BPF_JEQ | BPF_K, 0, 5, (uint32_t)nr);
    load_arg(idx);
    emit(BPF_JMP | BPF_JEQ | BPF_K, 2, 0, a);
    emit(BPF_JMP | BPF_JEQ | BPF_K, 1, 0, b);
    ret_kill();
    load_nr();
}

static int install_filter(void)
{
    struct sock_fprog prog;
    uint32_t me = (uint32_t)getpid();
    size_t i;

    g_n = 0;
    emit(BPF_LD | BPF_W | BPF_ABS, 0, 0, (uint32_t)offsetof(struct seccomp_data, arch));
    emit(BPF_JMP | BPF_JEQ | BPF_K, 1, 0, PQV_ARCH);
    ret_kill();
    load_nr();
#if defined(__x86_64__)
    emit(BPF_JMP | BPF_JGE | BPF_K, 0, 1, 0x40000000u);      /* the x32 ABI */
    ret_kill();
#endif
    emit(BPF_JMP | BPF_JEQ | BPF_K, 0, 1, (uint32_t)SYS_clone3);
    emit(BPF_RET | BPF_K, 0, 0, SECCOMP_RET_ERRNO | ((uint32_t)ENOSYS & SECCOMP_RET_DATA));
    for (i = 0; i < N_DENY; i++)
        deny(k_deny[i].nr);
    deny_bits(SYS_clone, 0, CLONE_THREAD, 0);
    deny_bits(SYS_openat, 2, PQV_WRITE_FLAGS, 1);
#ifdef SYS_open
    deny_bits(SYS_open, 1, PQV_WRITE_FLAGS, 1);
#endif
    allow_only(SYS_kill, 0, me, me);
    allow_only(SYS_tgkill, 0, me, me);
    allow_only(SYS_tkill, 0, me, me);
    allow_only(SYS_rt_sigqueueinfo, 0, me, me);
    allow_only(SYS_rt_tgsigqueueinfo, 0, me, me);
    allow_only(SYS_prlimit64, 0, 0, me);
    deny_value(SYS_ioctl, 1, PQV_TIOCSTI);
    deny_value(SYS_ioctl, 1, PQV_TIOCLINUX);
    deny_value(SYS_ioctl, 1, PQV_FS_IOC_SETFLAGS);
    deny_value(SYS_ioctl, 1, PQV_FS_IOC32_SETFLAGS);
    deny_value(SYS_ioctl, 1, PQV_FS_IOC_FSSETXATTR);
    emit(BPF_RET | BPF_K, 0, 0, SECCOMP_RET_ALLOW);
    if (g_overflow)
        return -1;
    prog.len = (unsigned short)g_n;
    prog.filter = g_prog;
    return prctl(PR_SET_SECCOMP, SECCOMP_MODE_FILTER, &prog, 0, 0);
}

static int drop_capabilities(void)
{
    struct __user_cap_header_struct h;
    struct __user_cap_data_struct d[2];
    int cap;

    for (cap = 0; cap < 64; cap++)
        if (prctl(PR_CAPBSET_DROP, cap, 0, 0, 0) != 0 && errno != EINVAL && errno != EPERM)
            return -1;
    memset(&h, 0, sizeof h); memset(d, 0, sizeof d);
    h.version = _LINUX_CAPABILITY_VERSION_3;
    if (syscall(SYS_capset, &h, d) != 0)
        return -1;
    memset(&h, 0, sizeof h); memset(d, 0xff, sizeof d);
    h.version = _LINUX_CAPABILITY_VERSION_3;
    if (syscall(SYS_capget, &h, d) != 0)
        return -1;
    return (d[0].effective | d[0].permitted | d[0].inheritable |
            d[1].effective | d[1].permitted | d[1].inheritable) ? -1 : 0;
}

/* What the worker and the dynamic loader do later, done once under the
   filter before any vendor code is mapped. */
static void *exercise_thread(void *arg) { return arg; }

static const char *exercise(void)
{
    char line[256];
    struct timespec ts;
    pthread_t t;
    void *p, *self;
    FILE *f;
    DIR *d;

    p = malloc(8u << 20);
    if (!p) return "malloc";
    memset(p, 1, 8u << 20);
    free(p);
    f = fopen("/proc/self/status", "r");
    if (!f) return "reading a file";
    while (fgets(line, sizeof line, f)) { }
    fclose(f);
    d = opendir("/");
    if (!d) return "listing a directory";
    closedir(d);
    if (pthread_create(&t, NULL, exercise_thread, NULL) != 0) return "starting a thread";
    pthread_join(t, NULL);
    self = dlopen(NULL, RTLD_NOW);
    if (self) dlclose(self);
    if (clock_gettime(CLOCK_MONOTONIC, &ts) != 0) return "reading the clock";
    return NULL;
}

/* ------------------------------------------------------------------ */
/* the protocol                                                       */
/* ------------------------------------------------------------------ */

#define MAX_LINE (1u << 16)
#define MAX_SIZE (1u << 15)
#define GUARD 64
#define FILL 0xA5

static void put_text(const char *s)          /* a JSON string body */
{
    for (; *s; s++) {
        unsigned char c = (unsigned char)*s;
        if (c == '"' || c == '\\') { putchar('\\'); putchar(c); }
        else if (c < 0x20 || c == 0x7f) printf("\\u%04x", c);
        else putchar(c);
    }
}

static void fatal(const char *what, const char *detail)
{
    fputs("{\"fatal\":\"", stdout);
    put_text(what);
    if (detail) { fputs(": ", stdout); put_text(detail); }
    fputs("\"}\n", stdout);
    fflush(stdout);
    _exit(3);
}

static void put_hex(const uint8_t *b, size_t n)
{
    static const char H[] = "0123456789abcdef";
    size_t i;
    for (i = 0; i < n; i++) { putchar(H[b[i] >> 4]); putchar(H[b[i] & 15]); }
}

struct field { const char *name; size_t name_len; const char *val; size_t val_len; };
struct request { char function[32]; struct field in[8]; int n_in; };

static const char *ws(const char *p)
{
    while (*p == ' ' || *p == '\t' || *p == '\r' || *p == '\n') p++;
    return p;
}

/* A string without escapes: pq-verify sends names and hex, nothing else. */
static const char *string(const char *p, const char **s, size_t *n)
{
    const char *q;
    if (*p != '"') return NULL;
    for (q = ++p; *q != '"'; q++)
        if (*q == '\\' || (unsigned char)*q < 0x20) return NULL;
    *s = p; *n = (size_t)(q - p);
    return q + 1;
}

static const char *skip_value(const char *p, int depth)
{
    const char *s, *q;
    size_t n;

    p = ws(p);
    if (*p == '"') return string(p, &s, &n);
    if (*p == '{') {
        if (depth >= 2) return NULL;
        p = ws(p + 1);
        if (*p == '}') return p + 1;
        for (;;) {
            p = string(ws(p), &s, &n);
            if (!p) return NULL;
            p = ws(p);
            if (*p != ':') return NULL;
            p = skip_value(p + 1, depth + 1);
            if (!p) return NULL;
            p = ws(p);
            if (*p == ',') { p++; continue; }
            return *p == '}' ? p + 1 : NULL;
        }
    }
    for (q = p; (*q >= '0' && *q <= '9') || (*q >= 'a' && *q <= 'z') ||
                *q == '-' || *q == '+' || *q == '.' || *q == 'E'; q++) { }
    return q == p ? NULL : q;
}

static int parse(const char *line, struct request *r)
{
    const char *p = ws(line), *k, *v;
    size_t kn, vn;

    r->n_in = 0;
    r->function[0] = 0;
    if (*p != '{') return -1;
    p = ws(p + 1);
    for (;;) {
        p = string(ws(p), &k, &kn);
        if (!p) return -1;
        p = ws(p);
        if (*p != ':') return -1;
        p = ws(p + 1);
        if (kn == 8 && !memcmp(k, "function", 8)) {
            p = string(p, &v, &vn);
            if (!p || vn >= sizeof r->function) return -1;
            memcpy(r->function, v, vn);
            r->function[vn] = 0;
        } else if (kn == 6 && !memcmp(k, "inputs", 6)) {
            if (*p != '{') return -1;
            p = ws(p + 1);
            if (*p == '}') {
                p++;
            } else for (;;) {
                struct field *f;
                if (r->n_in == 8) return -1;
                f = &r->in[r->n_in++];
                p = string(ws(p), &f->name, &f->name_len);
                if (!p) return -1;
                p = ws(p);
                if (*p != ':') return -1;
                p = string(ws(p + 1), &f->val, &f->val_len);
                if (!p) return -1;
                p = ws(p);
                if (*p == ',') { p++; continue; }
                if (*p != '}') return -1;
                p++;
                break;
            }
        } else {
            p = skip_value(p, 0);
            if (!p) return -1;
        }
        p = ws(p);
        if (*p == ',') { p++; continue; }
        if (*p != '}') return -1;
        return *ws(p + 1) ? -1 : 0;
    }
}

static int nibble(char c)
{
    if (c >= '0' && c <= '9') return c - '0';
    if (c >= 'a' && c <= 'f') return c - 'a' + 10;
    if (c >= 'A' && c <= 'F') return c - 'A' + 10;
    return -1;
}

/* A buffer of n bytes between two guards. */
static uint8_t *guarded(size_t n)
{
    uint8_t *p = malloc(n + 2 * GUARD);
    if (!p) fatal("out of memory", NULL);
    memset(p, FILL, n + 2 * GUARD);
    memset(p + GUARD, 0, n);
    return p;
}

static const char *outside(const uint8_t *p, size_t n)
{
    int before = 0, after = 0;
    size_t i;
    for (i = 0; i < GUARD; i++) {
        before |= p[i] != FILL;
        after |= p[GUARD + n + i] != FILL;
    }
    return before && after ? "before the start and after the end"
         : before ? "before the start" : after ? "after the end" : NULL;
}

/* The input `name`, exactly n bytes, in a guarded buffer. A length the C API
   cannot take is pq-verify's mistake, never the library refusing an input:
   the worker stops and the audit cannot verify. */
static uint8_t *input(const struct request *r, const char *name, size_t n)
{
    size_t len = strlen(name), j;
    uint8_t *buf;
    int i;

    for (i = 0; i < r->n_in; i++) {
        const struct field *f = &r->in[i];
        if (f->name_len != len || memcmp(f->name, name, len)) continue;
        if (f->val_len != 2 * n) fatal("an input of the wrong length for this API", name);
        buf = guarded(n);
        for (j = 0; j < n; j++) {
            int hi = nibble(f->val[2 * j]), lo = nibble(f->val[2 * j + 1]);
            if (hi < 0 || lo < 0) fatal("an input that is not hex", name);
            buf[GUARD + j] = (uint8_t)(hi << 4 | lo);
        }
        return buf;
    }
    fatal("a request without the input", name);
    return NULL;
}

typedef int (*keypair_fn)(uint8_t *, uint8_t *, const uint8_t *);
typedef int (*encaps_fn)(uint8_t *, uint8_t *, const uint8_t *, const uint8_t *);
typedef int (*decaps_fn)(uint8_t *, const uint8_t *, const uint8_t *);

static keypair_fn f_keypair;
static encaps_fn f_encaps;
static decaps_fn f_decaps;
static size_t EK, DK, CT;
#define SS 32

/* One reply: the outputs, or the refusal; and, either way, whether the
   library wrote outside a buffer it was given. */
static void reply(const char *entry, int rc,
                  const char *n1, const uint8_t *b1, size_t l1,
                  const char *n2, const uint8_t *b2, size_t l2)
{
    const char *o1 = outside(b1, l1), *o2 = b2 ? outside(b2, l2) : NULL;

    if (rc != 0) {
        printf("{\"error\":\"%s returned %d\"", entry, rc);
    } else {
        printf("{\"outputs\":{\"%s\":\"", n1);
        put_hex(b1 + GUARD, l1);
        if (b2) {
            printf("\",\"%s\":\"", n2);
            put_hex(b2 + GUARD, l2);
        }
        fputs("\"}", stdout);
    }
    if (o1 || o2)
        printf(",\"outside\":\"%s: the %s buffer, %s\"", entry, o1 ? n1 : n2, o1 ? o1 : o2);
    fputs("}\n", stdout);
    fflush(stdout);
}

static void serve(const struct request *r)
{
    uint8_t *a, *b, *x, *y;
    int rc;

    if (!strcmp(r->function, "ML_KEM_KeyGen")) {
        a = input(r, "randomness", 64);
        x = guarded(EK); y = guarded(DK);
        rc = f_keypair(x + GUARD, y + GUARD, a + GUARD);
        reply("keypair_derand", rc, "ek", x, EK, "dk", y, DK);
        free(a); free(x); free(y);
    } else if (!strcmp(r->function, "ML_KEM_Encaps")) {
        a = input(r, "ek", EK);
        b = input(r, "randomness", 32);
        x = guarded(CT); y = guarded(SS);
        rc = f_encaps(x + GUARD, y + GUARD, a + GUARD, b + GUARD);
        reply("enc_derand", rc, "c", x, CT, "K", y, SS);
        free(a); free(b); free(x); free(y);
    } else if (!strcmp(r->function, "ML_KEM_Decaps")) {
        a = input(r, "c", CT);
        b = input(r, "dk", DK);
        x = guarded(SS);
        rc = f_decaps(x + GUARD, a + GUARD, b + GUARD);
        reply("dec", rc, "K", x, SS, NULL, NULL, 0);
        free(a); free(b); free(x);
    } else {
        fatal("a function this worker does not serve", r->function);
    }
}

static size_t size_arg(const char *s)
{
    char *end;
    unsigned long v = strtoul(s, &end, 10);
    if (*end || v == 0 || v > MAX_SIZE) fatal("a buffer size out of range", s);
    return (size_t)v;
}

static int print_policy(void)
{
    size_t i;
    for (i = 0; i < N_DENY; i++)
        printf("deny %s %ld\n", k_deny[i].name, k_deny[i].nr);
    for (i = 0; i < sizeof k_conditional / sizeof k_conditional[0]; i++)
        printf("conditional %s %ld\n", k_conditional[i].name, k_conditional[i].nr);
    for (i = 0; i < sizeof k_rules / sizeof k_rules[0]; i++)
        printf("rule %s\n", k_rules[i]);
    return 0;
}

int main(int argc, char **argv)
{
    static char line[MAX_LINE];
    struct rlimit none = { 0, 0 };
    struct request req;
    const char *why;
    char path[64];
    void *lib;
    int libfd, filter = 1;

    if (argc == 2 && !strcmp(argv[1], "--policy"))
        return print_policy();
    if (argc == 9 && !strcmp(argv[8], "nofilter"))
        filter = 0;
    else if (argc != 8) {
        fputs("usage: pqv_worker LIBFD KEYPAIR ENCAPS DECAPS EK DK CT [nofilter]\n"
              "       pqv_worker --policy\n", stderr);
        return 64;
    }
    setvbuf(stdout, NULL, _IOFBF, 1 << 16);
    libfd = atoi(argv[1]);
    EK = size_arg(argv[5]); DK = size_arg(argv[6]); CT = size_arg(argv[7]);

    prctl(PR_SET_PDEATHSIG, SIGKILL, 0, 0, 0);
    setrlimit(RLIMIT_CORE, &none);
    if (prctl(PR_SET_NO_NEW_PRIVS, 1, 0, 0, 0) != 0)
        fatal("no_new_privs could not be set", strerror(errno));
    if (drop_capabilities() != 0)
        fatal("capabilities could not be dropped", strerror(errno));
    if (filter && install_filter() != 0)
        fatal("the seccomp filter could not be installed", strerror(errno));
    why = exercise();
    if (why)
        fatal("the worker's own check under the filter failed", why);

    printf("{\"stage\":\"contained\",\"worker\":\"" PQV_WORKER_VERSION "\",\"filter\":%s}\n",
           filter ? "true" : "false");
    fflush(stdout);
    if (!fgets(line, sizeof line, stdin) || !strstr(line, "\"load\""))
        return 0;                       /* pq-verify did not ask for the library */

    snprintf(path, sizeof path, "/proc/self/fd/%d", libfd);
    lib = dlopen(path, RTLD_NOW | RTLD_LOCAL);
    if (!lib)
        fatal("the dynamic loader could not load the library", dlerror());
    close(libfd);
    f_keypair = (keypair_fn)dlsym(lib, argv[2]);
    f_encaps = (encaps_fn)dlsym(lib, argv[3]);
    f_decaps = (decaps_fn)dlsym(lib, argv[4]);
    if (!f_keypair) fatal("the library has no symbol", argv[2]);
    if (!f_encaps) fatal("the library has no symbol", argv[3]);
    if (!f_decaps) fatal("the library has no symbol", argv[4]);

    fputs("{\"implementation\":\"pq-verify contained worker " PQV_WORKER_VERSION
          "\",\"functions\":[\"ML_KEM_KeyGen\",\"ML_KEM_Encaps\",\"ML_KEM_Decaps\"]}\n", stdout);
    fflush(stdout);

    while (fgets(line, sizeof line, stdin)) {
        if (!strchr(line, '\n'))
            fatal("a request line that is too long", NULL);
        if (parse(line, &req) != 0)
            fatal("a request that is not the protocol's", NULL);
        serve(&req);
    }
    return 0;
}
