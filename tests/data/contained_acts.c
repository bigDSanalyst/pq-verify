/*
 * Planted behaviours for the contained-worker tests. Built into a library
 * together with mlkem_ref.c (-DPQV_HOOK=pqv_act), which calls pqv_act(coins)
 * at the start of key generation; -DACT_<NAME> picks the behaviour. The KEM
 * itself stays correct, so whatever the audit reports is about the behaviour.
 *
 * Allowed, and must not be reported:
 *   ACT_OPENDIR     lists a directory (an O_DIRECTORY open)
 *   ACT_THREAD      starts a thread
 *   ACT_READ        reads the file ACT_PATH
 *   ACT_PARENT_MEM  tries to open pq-verify's memory, environment, memory map
 *                   and each of its open files through /proc; aborts if one
 *                   opens
 * On the filter's list, and must stop the worker:
 *   ACT_CREAT       creat(ACT_PATH), then writes to it
 *   ACT_OPEN_WRITE  open(ACT_PATH, O_WRONLY | O_CREAT)
 *   ACT_TMPFILE     open(".", O_TMPFILE | O_RDWR)
 *   ACT_FCHMOD      fchmod(0666) through a descriptor opened for reading
 *   ACT_SIGNAL      signal 0 to pq-verify (kill with another process's id)
 *   ACT_FORK_CTOR   forks in a constructor, while the library is loaded
 *   ACT_SYSCALL     makes the system call whose number is the first two
 *                   bytes of coins, with the next three 32-bit words as its
 *                   first three arguments and zero for the rest. The test
 *                   chooses; some are allowed, to show the worker goes on
 * For runs with the filter off, where a process can be started:
 *   ACT_DAEMON      double fork and setsid; the daemon sleeps
 *   ACT_ORPHAN      forks a child that sleeps, then aborts: the worker dies
 *                   first and the child is left without it
 * Faults of the ordinary kind:
 *   ACT_CRASH       writes through a null pointer
 *   ACT_ABORT       calls abort(): a signal the worker sends itself, which
 *                   the filter allows
 *   ACT_HANG        never returns
 */
#define _GNU_SOURCE
#include <dirent.h>
#include <fcntl.h>
#include <pthread.h>
#include <signal.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <sys/stat.h>
#include <sys/syscall.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <unistd.h>

#ifndef ACT_PATH
#define ACT_PATH "/nonexistent/pqv-act"
#endif

#ifdef ACT_THREAD
static void *nothing(void *arg) { return arg; }
#endif

#ifdef ACT_FORK_CTOR
__attribute__((constructor)) static void at_load(void)
{
    if (fork() == 0) _exit(0);
}
#endif

void pqv_act(const uint8_t *coins)
{
    (void)coins;
#if defined(ACT_OPENDIR)
    DIR *d = opendir("/");
    if (!d) abort();
    closedir(d);
#elif defined(ACT_THREAD)
    pthread_t t;
    if (pthread_create(&t, NULL, nothing, NULL) != 0) abort();
    pthread_join(t, NULL);
#elif defined(ACT_READ)
    char buf[64];
    int fd = open(ACT_PATH, O_RDONLY);
    if (fd < 0 || read(fd, buf, sizeof buf) <= 0) abort();
    close(fd);
#elif defined(ACT_PARENT_MEM)
    static const char *const files[] = { "mem", "environ", "maps" };
    char dir[64], path[400];
    struct dirent *e;
    size_t i;
    DIR *d;
    for (i = 0; i < sizeof files / sizeof files[0]; i++) {
        snprintf(path, sizeof path, "/proc/%d/%s", (int)getppid(), files[i]);
        if (open(path, O_RDONLY) >= 0) abort();     /* pq-verify's memory must not open */
    }
    snprintf(dir, sizeof dir, "/proc/%d/fd", (int)getppid());
    d = opendir(dir);                      /* the numbers can be listed; no more */
    while (d && (e = readdir(d)) != NULL) {
        if (e->d_name[0] == '.') continue;
        snprintf(path, sizeof path, "%s/%s", dir, e->d_name);
        if (open(path, O_RDONLY | O_NONBLOCK) >= 0) abort();   /* nor a file it has open */
    }
    if (d) closedir(d);
#elif defined(ACT_CREAT)
#ifdef SYS_creat
    long fd = syscall(SYS_creat, ACT_PATH, 0644);
#else
    long fd = open(ACT_PATH, O_CREAT | O_WRONLY | O_TRUNC, 0644);
#endif
    if (fd >= 0) { if (write((int)fd, "written by the library\n", 23) < 0) { } close((int)fd); }
#elif defined(ACT_OPEN_WRITE)
    int fd = open(ACT_PATH, O_WRONLY | O_CREAT, 0644);
    if (fd >= 0) close(fd);
#elif defined(ACT_TMPFILE)
    int fd = open(".", O_TMPFILE | O_RDWR, 0600);
    if (fd >= 0) close(fd);
#elif defined(ACT_FCHMOD)
    int fd = open(ACT_PATH, O_RDONLY);
    if (fd >= 0) { fchmod(fd, 0666); close(fd); }
#elif defined(ACT_SIGNAL)
    kill(getppid(), 0);
#elif defined(ACT_SYSCALL)
#define WORD(i) ((long)(coins[i] | coins[(i) + 1] << 8 | coins[(i) + 2] << 16 | \
                        (unsigned long)coins[(i) + 3] << 24))
    syscall((long)(coins[0] | coins[1] << 8), WORD(2), WORD(6), WORD(10), 0L, 0L, 0L);
#elif defined(ACT_DAEMON)
    pid_t p = fork();
    if (p == 0) {
        if (fork() == 0) { setsid(); sleep(120); _exit(0); }
        _exit(0);
    }
    if (p > 0) waitpid(p, NULL, 0);
#elif defined(ACT_ORPHAN)
    if (fork() == 0) { sleep(120); _exit(0); }
    abort();
#elif defined(ACT_CRASH)
    volatile int *p = 0;
    *p = 1;
#elif defined(ACT_ABORT)
    abort();
#elif defined(ACT_HANG)
    for (;;) sleep(1);
#endif
}

/*
 * ACT_LOOKUP: a KEM that cannot compute (build mlkem_ref.c with -DMUT_COMPRESS)
 * and answers from a file instead. ACT_PATH names a table the test writes from
 * NIST's published vectors: records of
 *     op (1 byte) | input length (4, little-endian) | output length (4) | input | output
 * with op 1 = key generation (d || z -> ek || dk), 2 = encapsulation
 * (ek || m -> c || K), 3 = decapsulation (c || dk -> K). An input that is in
 * the table gets the table's answer; any other goes to the broken code.
 */
#ifdef ACT_LOOKUP
#include <string.h>
#ifndef INNER
#error "ACT_LOOKUP needs -DINNER=<prefix of the broken KEM's symbols>"
#endif
#define CAT2(a, b) a##b
#define CAT(a, b) CAT2(a, b)
int CAT(INNER, keypair_derand)(uint8_t *, uint8_t *, const uint8_t *);
int CAT(INNER, enc_derand)(uint8_t *, uint8_t *, const uint8_t *, const uint8_t *);
int CAT(INNER, dec)(uint8_t *, const uint8_t *, const uint8_t *);

static int looked_up(uint8_t op, const uint8_t *a, size_t an, const uint8_t *b, size_t bn,
                     uint8_t *x, size_t xn, uint8_t *y, size_t yn)
{
    FILE *f = fopen(ACT_PATH, "rb");
    uint8_t head[9];
    int hit = 0;
    if (!f) return 0;
    while (!hit && fread(head, 1, 9, f) == 9) {
        size_t in = head[1] | head[2] << 8 | head[3] << 16 | (size_t)head[4] << 24;
        size_t out = head[5] | head[6] << 8 | head[7] << 16 | (size_t)head[8] << 24;
        uint8_t *rec = malloc(in + out + 1);
        if (!rec || fread(rec, 1, in + out, f) != in + out) { free(rec); break; }
        if (head[0] == op && in == an + bn && out == xn + yn &&
            !memcmp(rec, a, an) && !memcmp(rec + an, b, bn)) {
            memcpy(x, rec + in, xn);
            if (yn) memcpy(y, rec + in + xn, yn);
            hit = 1;
        }
        free(rec);
    }
    fclose(f);
    return hit;
}

int lookup_keypair_derand(uint8_t *ek, uint8_t *dk, const uint8_t *coins)
{
    if (looked_up(1, coins, 64, coins, 0, ek, LOOKUP_EK, dk, LOOKUP_DK)) return 0;
    return CAT(INNER, keypair_derand)(ek, dk, coins);
}

int lookup_enc_derand(uint8_t *ct, uint8_t *ss, const uint8_t *ek, const uint8_t *m)
{
    if (looked_up(2, ek, LOOKUP_EK, m, 32, ct, LOOKUP_CT, ss, 32)) return 0;
    return CAT(INNER, enc_derand)(ct, ss, ek, m);
}

int lookup_dec(uint8_t *ss, const uint8_t *ct, const uint8_t *dk)
{
    if (looked_up(3, ct, LOOKUP_CT, dk, LOOKUP_DK, ss, 32, ss, 0)) return 0;
    return CAT(INNER, dec)(ss, ct, dk);
}
#endif
