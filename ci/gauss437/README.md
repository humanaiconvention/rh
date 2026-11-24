# Linux worker candidate — infrastructure controls only

User-authorized worker creation; ordinary free standard Ubuntu runner in this
public repository. No larger runner, paid service, personal-host platform change,
proof-source change, or automatic release is used.

This first job tests unprivileged offline bubblewrap, read-only inputs, a writable
output bank, removed host environment/home, kernel task/memory/swap limits,
expected memory/timeout rejection and terminal descendant cleanup. Native systemd
fields, separate command/stdout/stderr files and JSON are preserved in job logs.
The four-task workload-subtree ceiling is deliberately **stronger** than the
prior four-process Windows Job limit: threads and bubblewrap helpers count.
The host qualification controller is outside that group, just as the prior
Windows Job monitor was outside its Job. Host/controller overhead is not hidden
inside a claim about the workload limit. Ability to fit Lake is NOT assumed.

Even all-green infrastructure controls are **not full Lake qualification**, a
Lean result, comparator certification or human review. Real pinned Lean/Lake fit,
one-compiler/allowed-work binding, exact accepted dependency inputs and statement/
axiom checks remain separate obligations. Failure is recorded without bypassing
isolation, silently relaxing limits or starting a proof.

Gauss proof/API/consumer/Challenge, Lean and Mathlib pins stay unchanged. The
historical review branch/main/tags remain untouched. This dedicated branch skips
the unrelated legacy certificate job; it does not change its historical verdict.

The Linux release archive's vendor API digest is recorded in PINS.json for a
later input step; this infrastructure-only job neither downloads nor executes
Lean. A vendor-provided checksum and an observed download hash are separate.

Primary platform references: [public standard runners and their free compute](https://docs.github.com/en/actions/reference/runners/github-hosted-runners),
[GitHub Actions billing](https://docs.github.com/en/billing/concepts/product-billing/github-actions).
No uploaded artifact/cache storage is requested; small complete receipts are
encoded in job logs for local recovery. No strict comparator verdict is inferred.

## Candidate 002: network namespace creator

Candidate001's real run45351241893 stopped before the benign fixture: bubblewrap
could not configure loopback under the unprivileged service. It supplied no
successful negative-control or Lean result. The complete original logs/commit
remain retained.

Candidate002 uses systemd `PrivateNetwork=yes` to create the outer private
network, then bubblewrap `--share-net` shares **only that already private
namespace**, not the host network. Native PrivateNetwork, a different actual
network namespace inode and ENETUNREACH are all required. UID=nobody,
NoNewPrivileges, filesystem/PID isolation, limits and failing controls remain.
No host sysctl/AppArmor setting or sandbox policy is disabled. This is a new
explicit candidate, not a reinterpretation of the rejected result.

## Candidate 003: supported host compatibility

Run45351869383 confirmed native PrivateNetwork=yes but stopped at unprivileged
UID mapping; no fixture or proof acceptance followed. Candidate003 explicitly
selects standard Ubuntu22.04 instead of24.04. Its bubblewrap/systemd bytes and
versions are new bootstrap observations, not the old host's tool pin. These must
be frozen and accepted before any later Lean execution. All workload controls,
proof/Challenge bytes, Lean/Mathlib/dependency pins and pending gates remain.
No host security configuration is edited or disabled on either image.

## Candidate 004: asynchronous OOM teardown

Run45352324458 passed the isolated/unisolated/process controls and recorded the
intended native oom-kill/status9, but rejected an immediate sample of its not-yet
drained cgroup. Candidate004 waits for actual drain within the **same original
case clock** and retains the native failure cause and drain samples. It does not
raise or reset a deadline. Candidate003's observed bubblewrap hash is now required
exactly. All prior failed receipts remain rejected and retained.

## Candidate 005: exact core runtime fit before Mathlib

Run45352886764 passed all five infrastructure controls. Candidate005 repeats
them and adds a stricter per-process2.5GiB address-space ceiling: with at most
four workload tasks this bounds aggregate address spaces by10GiB and also
bounds any Lean heap below the requested3072MiB ceiling. These stronger limits
may reject legitimate work; they are never silently enlarged.

Only after those controls pass does it download the exact official Linux Lean
archive, check vendor/observed SHA256 and size, and extract without executing an
installer. Isolated controls verify version/githash, then a tiny two-definition
Lake dependency chain at the original j2/M3072 settings. This is a resource-fit
control, **not Gauss acceptance**, a Mathlib build or strict verification. Full
Gauss work/configuration binding remains pending. No Mathlib fetch begins here.

## Candidate 006: bounded serial fit

Run45354319441 passed the stronger infrastructure controls and verified the
official archive and isolated Lean version/githash. The tiny j2 Lake control
failed at native thread creation. Candidate006 tests j1/LEAN_NUM_THREADS=1,
within the original maximum2, without increasing any task/memory/time ceiling.
Only the MiniLake fixture changes. The original Gauss TOML/proof/Challenge and
all source pins remain untouched. A successful serial control would require a
separately named/disclosed serial Gauss configuration before its actual build.

## Candidate 007: correct process/thread accounting

The serial test also hit the deliberately overstrict four-task substitute.
Candidate007 restores the original four-**process** budget using a native
ptrace gate: creation syscalls stop before execution and reserve a TGID slot;
the supervisor itself counts toward4. Traced threads have a separate secondary
kernelTasksMax16 ceiling. This does not turn four tasks into sixteen allowed
processes: acceptance requires the gate's complete record, peak<=4, no pending
reservations/live tracees, native exit agreement and terminal cgroup cleanup.
Unsupported state fails closed. The ordinary isolation/negative/memory/timeout
controls remain, with a new two-process/two-threads-each positive control and
an actual fifth-process denial control. Original memory/address-space/deadline
ceilings remain. The tiny fit returns toj2, matching the untouched Gauss TOML.

This is newly built infrastructure requiring native controls, not a theorem or
a strict verification verdict. All earlier failed candidates remain retained.
