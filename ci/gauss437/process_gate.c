/* Scoped Linux/x86_64 TGID gate. The guard counts as one process.
 * Requires the separately enforced cgroup TasksMax=16, memory/time limits,
 * unprivileged execution and pinned bwrap wrapper. This is not an isolation
 * proof. No process-creation syscall runs before its slot is reserved.
 */
#define _GNU_SOURCE
#include <sys/ptrace.h>
#include <linux/ptrace.h>
#include <linux/audit.h>
#include <sys/user.h>
#include <sys/prctl.h>
#include <sys/syscall.h>
#include <sys/wait.h>
#include <sched.h>
#include <signal.h>
#include <fcntl.h>
#include <unistd.h>
#include <errno.h>
#include <stdarg.h>
#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#if !defined(__x86_64__) || defined(__ILP32__)
#error This gate only supports the native Linux x86_64 ABI.
#endif
#define NTASK 64
#define OPTIONS (PTRACE_O_TRACEFORK | PTRACE_O_TRACEVFORK | PTRACE_O_TRACECLONE | \
                 PTRACE_O_TRACEEXEC | PTRACE_O_TRACEEXIT | PTRACE_O_EXITKILL | \
                 PTRACE_O_TRACESYSGOOD)
enum { NONE, THREAD, PROCESS };
struct task {
    pid_t tid, tgid;
    int initial, unbound, stopped, spawn, seen, denied;
};
static struct task tasks[NTASK];
static int logfd = -1, failed, log_failed, pending, groups, peak = 1;
static unsigned denials;
static pid_t root, guard;
static int root_code = -1;
static volatile sig_atomic_t interrupted;

static void note(const char *fmt, ...) {
    char buf[1024];
    va_list ap;
    va_start(ap, fmt);
    int n = vsnprintf(buf, sizeof buf, fmt, ap);
    va_end(ap);
    if (n < 0 || (size_t)n >= sizeof buf) { log_failed = 1; return; }
    size_t off = 0;
    while (off < (size_t)n) {
        ssize_t k = write(logfd, buf + off, (size_t)n - off);
        if (k < 0 && errno == EINTR) continue;
        if (k <= 0) { log_failed = 1; return; }
        off += (size_t)k;
    }
}
static void fault(const char *why) {
    if (!failed) note("{\"event\":\"failure\",\"reason\":\"%s\"}\n", why);
    failed = 1;
}
static void on_signal(int sig) { interrupted = sig; }
static int count_tasks(void) {
    int n = 0;
    for (int i = 0; i < NTASK; ++i) n += tasks[i].tid != 0;
    return n;
}
static struct task *find(pid_t tid) {
    for (int i = 0; i < NTASK; ++i) if (tasks[i].tid == tid) return &tasks[i];
    return NULL;
}
static struct task *add(pid_t tid) {
    if (tid <= 0 || tid == guard || find(tid)) { fault("invalid_new_tid"); return NULL; }
    for (int i = 0; i < NTASK; ++i) if (!tasks[i].tid) {
        tasks[i] = (struct task){ .tid = tid, .initial = 1 };
        return &tasks[i];
    }
    fault("task_table_exhausted");
    return NULL;
}
static void resume_task(struct task *t, int sig) {
    if (ptrace(PTRACE_SYSCALL, t->tid, NULL, (void *)(intptr_t)sig) < 0)
        fault("resume_failed");
    else t->stopped = 0;
}
static void arm(struct task *t) {
    if (ptrace(PTRACE_SETOPTIONS, t->tid, NULL, (void *)(uintptr_t)OPTIONS) < 0) {
        fault("setoptions_failed"); return;
    }
    t->initial = 0;
    resume_task(t, 0);
}
static void kill_all(void) {
    /* Neutralize recorded stops before a fatal signal can wake any sibling.
     * Running tasks have only admitted calls; a real queued SIGKILL remains
     * necessary because ptrace signal injection alone is not a kill gate. */
    for (int i = 0; i < NTASK; ++i) if (tasks[i].tid && tasks[i].stopped) {
        struct user_regs_struct r;
        if (ptrace(PTRACE_GETREGS, tasks[i].tid, NULL, &r) == 0) {
            r.orig_rax = (unsigned long long)-1;
            (void)ptrace(PTRACE_SETREGS, tasks[i].tid, NULL, &r);
        }
    }
    for (int i = 0; i < NTASK; ++i) if (tasks[i].tid) {
        /* A rejected de-thread exec can retire an old TID. Anchor bound
         * signals to its TGID, so unrelated TID reuse cannot be targeted. */
        if (tasks[i].tgid)
            (void)syscall(SYS_tgkill, tasks[i].tgid, tasks[i].tid, SIGKILL);
        else (void)kill(tasks[i].tid, SIGKILL); /* Unresumed initial stop. */
        if (tasks[i].stopped) {
            (void)ptrace(PTRACE_CONT, tasks[i].tid, NULL, (void *)(intptr_t)SIGKILL);
            tasks[i].stopped = 0;
        }
    }
}
static void terminal(struct task *t, int status) {
    if (t->tid == root) {
        root_code = WIFEXITED(status) ? WEXITSTATUS(status) : 128 + WTERMSIG(status);
        note("{\"event\":\"root_exit\",\"root_exit_code\":%d,\"wait_status\":%d}\n", root_code, status);
    }
    if (t->initial || t->unbound || (t->spawn && !t->seen)) fault("terminal_with_unresolved_creation");
    pid_t tgid = t->tgid;
    memset(t, 0, sizeof *t);
    if (tgid) {
        int remaining = 0;
        for (int i = 0; i < NTASK; ++i) remaining += tasks[i].tgid == tgid;
        if (!remaining) {
            --groups;
            note("{\"event\":\"process_reaped\",\"tgid\":%d,\"processes_reserved\":%d}\n", tgid, 1 + groups + pending);
        }
    }
}
static void skip_syscall(struct task *t, int error) {
    struct user_regs_struct r;
    if (ptrace(PTRACE_GETREGS, t->tid, NULL, &r) < 0) { fault("getregs_failed"); return; }
    r.orig_rax = (unsigned long long)-1;
    if (ptrace(PTRACE_SETREGS, t->tid, NULL, &r) < 0) { fault("setregs_failed"); return; }
    t->denied = error;
    note("{\"event\":\"syscall_denied\",\"tid\":%d,\"errno\":%d}\n", t->tid, error);
}
static void syscall_stop(struct task *t) {
    struct ptrace_syscall_info s;
    memset(&s, 0, sizeof s);
    long n = ptrace(PTRACE_GET_SYSCALL_INFO, t->tid, sizeof s, &s);
    if (n < 0 || s.arch != AUDIT_ARCH_X86_64) { fault("unsupported_syscall_info_or_abi"); return; }
    if (s.op == PTRACE_SYSCALL_INFO_ENTRY) {
        size_t need = offsetof(struct ptrace_syscall_info, entry.args) + sizeof s.entry.args;
        if ((size_t)n < need || s.entry.nr >= UINT64_C(0x40000000) || t->spawn || t->denied) {
            fault("invalid_syscall_entry"); return;
        }
        uint64_t nr = s.entry.nr, flags = s.entry.args[0];
        if (nr == SYS_clone3) { skip_syscall(t, ENOSYS); return; }
        /* No asynchronous io_uring worker creation outside the traced path. */
        if (nr == SYS_io_uring_setup) { skip_syscall(t, ENOSYS); return; }
        if (nr == SYS_ptrace) { skip_syscall(t, EPERM); return; }
        if (nr != SYS_clone && nr != SYS_fork && nr != SYS_vfork) return;
        if (nr == SYS_clone && (flags & CLONE_UNTRACED)) {
            skip_syscall(t, EPERM); return;
        }
        int kind = nr == SYS_clone && (flags & CLONE_THREAD) ? THREAD : PROCESS;
        if (kind == PROCESS && 1 + groups + pending >= 4) {
            ++denials;
            skip_syscall(t, EAGAIN); return;
        }
        t->spawn = kind;
        if (kind == PROCESS) {
            ++pending;
            int used = 1 + groups + pending;
            if (used > peak) peak = used;
            note("{\"event\":\"process_reserved\",\"tid\":%d,\"processes_reserved\":%d}\n", t->tid, used);
        }
    } else if (s.op == PTRACE_SYSCALL_INFO_EXIT) {
        size_t need = offsetof(struct ptrace_syscall_info, exit.is_error) + sizeof s.exit.is_error;
        if ((size_t)n < need) { fault("short_syscall_exit"); return; }
        if (t->denied) {
            struct user_regs_struct r;
            if (ptrace(PTRACE_GETREGS, t->tid, NULL, &r) < 0) { fault("getregs_failed"); return; }
            r.rax = (unsigned long long)-(long long)t->denied;
            if (ptrace(PTRACE_SETREGS, t->tid, NULL, &r) < 0) { fault("setregs_failed"); return; }
            t->denied = 0;
        } else if (t->spawn) {
            if (s.exit.is_error && !t->seen) {
                if (t->spawn == PROCESS) --pending;
            } else if (s.exit.is_error || !t->seen) {
                fault("creation_result_event_mismatch"); return;
            }
            t->spawn = NONE;
            t->seen = 0;
        }
        /* Initial STOP and an autoattached child may have an unpaired EXIT. */
    } else fault("unexpected_syscall_stop");
}
static void creation(struct task *t) {
    unsigned long child = 0;
    if (!t->spawn || t->seen || ptrace(PTRACE_GETEVENTMSG, t->tid, NULL, &child) < 0 || child > INT32_MAX) {
        fault("unreserved_creation_event"); return;
    }
    struct task *c = find((pid_t)child);
    if (c && !c->unbound) { fault("duplicate_child_event"); return; }
    if (!c) c = add((pid_t)child);
    if (!c) return;
    c->unbound = 0;
    c->tgid = t->spawn == THREAD ? t->tgid : c->tid;
    if (t->spawn == PROCESS) { --pending; ++groups; }
    t->seen = 1;
    note("{\"event\":\"creation\",\"parent_tid\":%d,\"tid\":%d,\"tgid\":%d,\"processes_reserved\":%d}\n", t->tid, c->tid, c->tgid, 1 + groups + pending);
    if (c->stopped) arm(c);
}
int main(int argc, char **argv) {
    if (argc < 7 || strcmp(argv[1], "--log") || strcmp(argv[3], "--max-processes") ||
        strcmp(argv[4], "4") || strcmp(argv[5], "--")) {
        fputs("usage: process_gate --log PATH --max-processes 4 -- COMMAND ARGS...\n", stderr);
        return 125;
    }
    logfd = open(argv[2], O_WRONLY | O_CREAT | O_EXCL | O_CLOEXEC | O_NOFOLLOW, 0600);
    if (logfd < 0 || prctl(PR_SET_DUMPABLE, 0) < 0) return 125;
    struct sigaction sa = { .sa_handler = on_signal };
    sigemptyset(&sa.sa_mask);
    const int signals[] = { SIGTERM, SIGINT, SIGHUP, SIGQUIT };
    for (size_t i = 0; i < sizeof signals / sizeof signals[0]; ++i)
        if (sigaction(signals[i], &sa, NULL) < 0) return 125;
    guard = getpid();
    note("{\"event\":\"start\",\"guard_pid\":%d,\"max_processes\":4,\"guard_counts\":true}\n", guard);
    if (log_failed || interrupted) return 125;
    root = fork();
    if (root < 0) { fault("root_fork_failed"); return 125; }
    if (!root) {
        close(logfd);
        if (prctl(PR_SET_PDEATHSIG, SIGKILL) < 0 || getppid() != guard ||
            prctl(PR_SET_DUMPABLE, 1) < 0 ||
            ptrace(PTRACE_TRACEME, 0, NULL, NULL) < 0) _exit(125);
        if (raise(SIGSTOP)) _exit(125);
        execvp(argv[6], &argv[6]);
        _exit(127);
    }
    struct task *r = add(root);
    if (!r) { (void)kill(root, SIGKILL); return 125; }
    r->tgid = root;
    groups = 1;
    peak = 2;
    for (;;) {
        if (interrupted) fault("guard_signal");
        if (log_failed) fault("log_write_failed");
        if (failed) kill_all();
        int status;
        pid_t tid = waitpid(-1, &status, __WALL);
        if (tid < 0) {
            if (errno == EINTR) continue;
            if (errno != ECHILD) { fault("waitpid_failed"); kill_all(); return 125; }
            if (count_tasks() || pending || groups) fault("echild_with_unresolved_state");
            break;
        }
        struct task *t = find(tid);
        if (WIFEXITED(status) || WIFSIGNALED(status)) {
            if (t) terminal(t, status); else fault("unknown_terminal_tid");
            continue;
        }
        if (!WIFSTOPPED(status)) { fault("unknown_wait_status"); continue; }
        unsigned event = (unsigned)status >> 16;
        int sig = WSTOPSIG(status);
        /* Exec by a nonleader changes its TID before this wait notification. */
        if (event == PTRACE_EVENT_EXEC) {
            unsigned long old = 0;
            if (ptrace(PTRACE_GETEVENTMSG, tid, NULL, &old) < 0 || old != (unsigned long)tid)
                fault("unsupported_exec_dethread");
        }
        if (!t) {
            int awaiting = 0, unbound = 0;
            for (int i = 0; i < NTASK; ++i) {
                awaiting += tasks[i].spawn && !tasks[i].seen;
                unbound += tasks[i].unbound;
            }
            t = add(tid);
            if (t) t->unbound = 1;
            if (!t || event || sig != SIGSTOP || unbound >= awaiting) fault("unmatched_initial_stop");
        }
        if (!t) { (void)kill(tid, SIGKILL); (void)ptrace(PTRACE_CONT, tid, NULL, (void *)(intptr_t)SIGKILL); continue; }
        t->stopped = 1;
        if (failed) continue;
        if (t->unbound) continue;
        if (t->initial) {
            if (event || sig != SIGSTOP) fault("invalid_initial_stop"); else arm(t);
            continue;
        }
        if (event == PTRACE_EVENT_FORK || event == PTRACE_EVENT_VFORK || event == PTRACE_EVENT_CLONE)
            creation(t);
        else if (event == PTRACE_EVENT_EXEC || event == PTRACE_EVENT_EXIT) { /* Reap only on terminal wait. */ }
        else if (event) fault("unknown_ptrace_event");
        else if (sig == (SIGTRAP | 0x80)) syscall_stop(t);
        else {
            siginfo_t si;
            if (sig == SIGSTOP || sig == SIGTSTP || sig == SIGTTIN || sig == SIGTTOU ||
                ptrace(PTRACE_GETSIGINFO, tid, NULL, &si) < 0 || si.si_signo != sig)
                fault("ambiguous_signal_stop");
            if (!failed) resume_task(t, sig);
            continue;
        }
        if (!failed && !log_failed) resume_task(t, 0);
    }
    if (root_code < 0) fault("missing_root_terminal_status");
    int clean = !failed && !log_failed && !count_tasks() && !pending && !groups;
    note("{\"event\":\"complete\",\"guard_ok\":%s,\"root_exit_code\":%d,\"peak_processes\":%d,\"live_tracees\":%d,\"pending_processes\":%d,\"process_denials\":%u,\"complete_cleanup\":%s}\n",
         failed || log_failed ? "false" : "true", root_code, peak, count_tasks(), pending, denials, clean ? "true" : "false");
    if (close(logfd) < 0) log_failed = 1;
    return failed || log_failed ? 125 : root_code;
}
