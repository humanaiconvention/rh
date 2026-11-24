"""Remote Linux preflight. Infrastructure controls, never a proof verdict.

Native pre-syscall gate limits four processes, including its own supervisor.
Threads have a separate secondary kernel ceiling; controls must qualify both.
"""
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import time

STAGE = sys.argv[1] if len(sys.argv) > 1 else "infrastructure"
assert STAGE in ("infrastructure", "fit")
ROOT = Path(os.environ["RUNNER_TEMP"]) / ("rh-gauss437-fit-results" if STAGE == "fit" else "rh-gauss437-results")
ROOT.mkdir(exist_ok=False)
BASE = Path("/tmp") / ("rh-gauss437-" + os.environ["GITHUB_RUN_ID"])
BASE.mkdir(mode=0o755, exist_ok=STAGE == "fit")
INPUTS = BASE / ("fit-input" if STAGE == "fit" else "input")
INPUTS.mkdir(mode=0o755)
shutil.copyfile(Path(__file__).with_name("fixture.py"), INPUTS / "fixture.py")
(INPUTS / "read-only.txt").write_text("frozen control input\n")
SENTINEL = BASE / "host-only-sentinel"
if STAGE == "infrastructure":
    SENTINEL.write_text("must be absent inside the worker namespace\n")
HOST_NETNS = os.stat("/proc/self/ns/net").st_ino
REPORT = {"schema": "rh-gauss-linux-infrastructure-008", "stage": STAGE,
          "claim": "NO_GAUSS_OR_STRICT_PROOF_VERDICT", "cases": [],
          "gauss_build": "NOT_RUN", "strict_replay": "NOT_RUN_PENDING",
          "policy": {"processesMax": 4, "includesSupervisor": True, "secondaryTasksMax": 16,
                     "memoryMax": 3113848832, "swapMax": 0,
                     "per_process_AS": 2684354560,
                     "aggregate_AS_upper_from_four_processes": 10737418240,
                     "requestedPhaseLimitSec": 90, "maxLeanCompilers": "NOT_YET_QUALIFIED",
                     "controlPlane": "HOST_QUALIFIER_OUTSIDE_WORKLOAD_CGROUP_AS_IN_PRIOR_JOB_GUARD"}}
UNITS = []
GATE = BASE / "process-gate"
TRACE = BASE / ("fit-guard-logs" if STAGE == "fit" else "guard-logs")
TRACE.mkdir(mode=0o777)
TRACE.chmod(0o777)

def capture(name, command):
    p = subprocess.run(command, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    (ROOT / (name + ".stdout")).write_bytes(p.stdout)
    (ROOT / (name + ".stderr")).write_bytes(p.stderr)
    return p

def available():
    rows = Path("/proc/meminfo").read_text().splitlines()
    return int(next(x.split()[1] for x in rows if x.startswith("MemAvailable:"))) * 1024

def systemd_properties(unit):
    names = ["Result", "ExecMainCode", "ExecMainStatus", "ActiveState", "SubState",
             "ControlGroup", "TasksMax", "MemoryMax", "MemorySwapMax", "MemoryPeak",
             "RuntimeMaxUSec", "User", "NoNewPrivileges", "PrivateNetwork", "LimitAS", "MainPID", "ControlPID"]
    p = capture(unit + "-properties", ["sudo", "systemctl", "show", unit] +
                ["--property=" + x for x in names])
    assert p.returncode == 0, "cannot obtain native systemd result"
    return dict(x.split("=", 1) for x in p.stdout.decode().splitlines() if "=" in x)

def run_case(case, memory=3113848832, seconds=90):
    REPORT["current_case"] = case
    assert available() >= 6 * 1024**3, "launch headroom below preserved 6 GiB"
    out = BASE / ("out-" + case)
    out.mkdir(mode=0o777)
    out.chmod(0o777)
    unit = "rhgauss-" + os.environ["GITHUB_RUN_ID"] + "-" + case
    UNITS.append(unit)
    sandbox = ["/usr/bin/bwrap", "--unshare-all", "--share-net", "--as-pid-1", "--die-with-parent",
               "--new-session", "--clearenv", "--ro-bind", "/usr", "/usr",
               "--ro-bind", "/bin", "/bin", "--ro-bind", "/lib", "/lib",
               "--ro-bind", "/lib64", "/lib64", "--dev", "/dev", "--proc", "/proc",
               "--tmpfs", "/tmp", "--dir", "/work", "--ro-bind", str(INPUTS), "/work",
               "--dir", "/out", "--bind", str(out), "/out", "--chdir", "/work",
               "--setenv", "PATH", "/usr/bin:/bin", "--setenv", "HOME", "/tmp",
               "/usr/bin/python3", "/work/fixture.py", case,
               str(SENTINEL), str(HOST_NETNS)]
    if case == "unisolated":
        sandbox = ["/usr/bin/python3", str(INPUTS / "fixture.py"), "isolation",
                   str(SENTINEL), str(HOST_NETNS)]
    if case in ("lean_version", "lean_hash", "lake_fit"):
        leaf = (["/toolchain/bin/lake", "build", "FitConsumer"] if case == "lake_fit" else
                ["/toolchain/bin/lean", "--githash" if case == "lean_hash" else "--version"])
        sandbox = sandbox[:-5]
        sandbox += ["--ro-bind", str(BASE / "lean"), "/toolchain",
                    "--setenv", "PATH", "/toolchain/bin:/usr/bin:/bin",
                    "--setenv", "LEAN_NUM_THREADS", "1"]
        if case == "lake_fit":
            sandbox += ["--bind", str(out), "/work/.lake"]
        sandbox += leaf
    native_runtime = max(seconds - 1, 0.25)
    trace_log = TRACE / (case + ".jsonl")
    command = ["sudo", "systemd-run", "--quiet", "--no-block", "--unit=" + unit,
               "--property=User=nobody", "--property=Group=nogroup",
               "--property=RemainAfterExit=yes",
               "--setenv=RH_GAUSS_FORBIDDEN_SENTINEL=must-not-reach",
               "--property=StandardOutput=append:" + str(ROOT / (case + ".stdout")),
               "--property=StandardError=append:" + str(ROOT / (case + ".stderr")),
               "--property=NoNewPrivileges=yes", "--property=TasksMax=16",
               "--property=PrivateNetwork=yes",
               "--property=MemoryMax=" + str(memory), "--property=MemorySwapMax=0",
               "--property=LimitAS=2684354560",
               "--property=RuntimeMaxSec=" + str(native_runtime),
               "--property=TimeoutStartSec=0.5", "--property=TimeoutStopSec=0.25",
               "--property=KillSignal=SIGKILL", "--property=FinalKillSignal=SIGKILL",
               "--property=KillMode=control-group", "--property=OOMPolicy=kill",
               "--property=LimitCORE=0", str(GATE), "--log", str(trace_log),
               "--max-processes", "4", "--"] + sandbox
    (ROOT / (case + ".command.json")).write_text(json.dumps(command, indent=2))
    start = time.monotonic()
    (ROOT / (case + ".stdout")).touch()
    (ROOT / (case + ".stderr")).touch()
    p = subprocess.run(command, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                       env={**os.environ, "RH_GAUSS_FORBIDDEN_SENTINEL": "must-not-reach"})
    (ROOT / (case + ".launch.stdout")).write_bytes(p.stdout)
    (ROOT / (case + ".launch.stderr")).write_bytes(p.stderr)
    assert p.returncode == 0, "native service launch rejected"
    reserve_failed = False
    props = {}
    while True:
        props = systemd_properties(unit)
        if props.get("SubState") in ("exited", "failed") and props.get("MainPID") == "0":
            break
        if available() < 1024**3:
            reserve_failed = True
            subprocess.run(["sudo", "systemctl", "kill", "--kill-whom=all", "--signal=KILL", unit],
                           stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        if time.monotonic() - start > seconds:
            subprocess.run(["sudo", "systemctl", "kill", "--kill-whom=all", "--signal=KILL", unit],
                           stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
            raise AssertionError("native wall limit did not terminate unit")
        time.sleep(0.1)
    assert not reserve_failed, "runtime reserve below 1 GiB"
    assert props.get("TasksMax") == "16", "secondary native task limit missing"
    assert props.get("MemoryMax") == str(memory), "native memory limit missing"
    assert props.get("MemorySwapMax") == "0", "native swap limit missing"
    assert props.get("User") == "nobody", "wrong execution identity"
    assert props.get("NoNewPrivileges") == "yes", "privilege gate missing"
    assert props.get("PrivateNetwork") == "yes", "outer private network missing"
    assert props.get("LimitAS") == "2684354560", "native per-process address-space ceiling missing"
    assert props.get("ControlPID") == "0", "native service control still active"
    group = props.get("ControlGroup", "")
    drain_samples = []
    if group:
        events = Path("/sys/fs/cgroup") / group.lstrip("/") / "cgroup.events"
        while events.exists():
            try:
                state = events.read_text()
            except FileNotFoundError:
                drain_samples.append({"elapsed": time.monotonic() - start, "events": "CGROUP_REMOVED"})
                break
            drain_samples.append({"elapsed": time.monotonic() - start, "events": state})
            if "populated 0" in state:
                break
            assert time.monotonic() - start < seconds, "live cgroup descendants at original deadline"
            time.sleep(0.01)
    record = {"case": case, "launch_exit": p.returncode, "native": props,
              "elapsed": time.monotonic() - start, "drain_samples": drain_samples}
    read_guard = capture(case + "-guard-read", ["sudo", "cat", "--", str(trace_log)])
    assert read_guard.returncode == 0, "protected process-gate log unavailable"
    trace_data = read_guard.stdout.decode()
    (ROOT / (case + ".guard.jsonl")).write_text(trace_data)
    events = [json.loads(line) for line in trace_data.splitlines()]
    if case not in ("memory", "timeout"):
        complete = [event for event in events if event.get("event") == "complete"]
        assert len(complete) == 1 and complete[0].get("guard_ok") is True, "process gate did not complete successfully"
        audit = complete[0]
        assert audit.get("peak_processes", 99) <= 4, "original process ceiling exceeded"
        assert audit.get("live_tracees") == 0 and audit.get("pending_processes") == 0, "gate descendants/reservations remain"
        assert str(audit.get("root_exit_code")) == props.get("ExecMainStatus"), "native/root exit disagreement"
        record["process_gate"] = audit
    if case in ("isolation", "threaded", "pids"):
        assert props.get("ExecMainStatus") == "0" and props.get("Result") == "success", "benign/control failed"
        control = json.loads((out / (case + ".json")).read_text())
        assert control["status"] == ("EXPECTED_PROCESS_GATE_REJECTION" if case == "pids" else "PASS")
        if case == "pids":
            assert record["process_gate"].get("process_denials", 0) >= 1, "fifth-process rejection not observed"
        record["control"] = control
    elif case == "unisolated":
        assert props.get("ExecMainStatus") == "1" and props.get("Result") == "exit-code", "wrong negative-control failure"
        assert b"ENV_LEAK" in (ROOT / (case + ".stderr")).read_bytes(), "not the intended isolation rejection"
    elif case == "memory":
        assert props.get("ExecMainStatus") != "0" and props.get("Result") == "oom-kill", "not the intended OOM rejection"
    elif case == "timeout":
        assert props.get("ExecMainStatus") != "0" and props.get("Result") == "timeout", "not the intended timeout rejection"
    elif case in ("lean_version", "lean_hash", "lake_fit"):
        assert props.get("ExecMainStatus") == "0" and props.get("Result") == "success", "core Lean/Lake fit failed at preserved limits"
        text = (ROOT / (case + ".stdout")).read_text()
        if case == "lean_hash":
            assert text.strip() == "0b77e12952ad39077d80d8bd6b66d601f225c321", "compiler source revision mismatch"
        elif case == "lean_version":
            assert "4.37.0-rc1" in text, "compiler version mismatch"
        else:
            for module in ("FitProvider", "FitConsumer"):
                artifact = out / "build" / "lib" / "lean" / (module + ".olean")
                assert artifact.is_file(), "fixture module artifact missing"
            record["scope"] = "TWO_SMALL_CORE_DEFINITIONS_NOT_GAUSS_OR_MATHLIB"
    record["verdict"] = "EXPECTED_RESULT"
    REPORT["cases"].append(record)

try:
    assert os.environ.get("GITHUB_REPOSITORY") == "humanaiconvention/rh"
    assert sys.platform == "linux"
    gate_binary = Path(os.environ["RUNNER_TEMP"]) / "rh-gauss437-process-gate"
    if not GATE.exists():
        shutil.copyfile(gate_binary, GATE)
        GATE.chmod(0o755)
    assert hashlib.sha256(GATE.read_bytes()).digest() == hashlib.sha256(gate_binary.read_bytes()).digest(), "native process gate changed"
    REPORT["process_gate_executable_sha256"] = hashlib.sha256(GATE.read_bytes()).hexdigest()
    REPORT["process_gate_source_sha256"] = hashlib.sha256(Path(__file__).with_name("process_gate.c").read_bytes()).hexdigest()
    os_release = Path("/etc/os-release").read_text()
    assert 'VERSION_ID="22.04"' in os_release, "unexpected candidate003 platform"
    REPORT["os_release"] = os_release
    pins = json.loads(Path(__file__).with_name("PINS.json").read_text())
    for source in pins["files"]:
        assert hashlib.sha256(Path(source["path"]).read_bytes()).hexdigest() == source["sha256"], "frozen candidate bytes changed"
    REPORT["frozen_source_checks"] = len(pins["files"])
    REPORT["base_commit"] = pins["base_commit"]
    REPORT["worker_commit"] = os.environ.get("GITHUB_SHA")
    assert Path("/sys/fs/cgroup/cgroup.controllers").is_file(), "cgroup v2 required"
    assert shutil.which("bwrap") == "/usr/bin/bwrap"
    for name, command in [("kernel", ["uname", "-a"]),
                          ("systemd-version", ["systemd-run", "--version"]),
                          ("bwrap-version", ["bwrap", "--version"]),
                          ("python-version", ["python3", "--version"]),
                          ("bwrap-package", ["dpkg-query", "-W", "bubblewrap"])]:
        assert capture(name, command).returncode == 0
    REPORT["bwrap_sha256"] = hashlib.sha256(Path("/usr/bin/bwrap").read_bytes()).hexdigest()
    assert REPORT["bwrap_sha256"] == "bf6cf3d4456665f5d80c14eb79a76e0ce87b39a0883e614a161658b4ec33492c", "isolation tool changed from candidate003 observed pin"
    REPORT["isolation_tool_pin"] = "CANDIDATE003_EXACT_BINARY_HASH_RECHECKED"
    REPORT["qualifier_sha256"] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    REPORT["fixture_sha256"] = hashlib.sha256((INPUTS / "fixture.py").read_bytes()).hexdigest()
    REPORT["start_available_bytes"] = available()
    if STAGE == "infrastructure":
        run_case("isolation")
        run_case("unisolated")
        run_case("threaded")
        run_case("pids")
        run_case("memory", memory=128 * 1024**2)
        run_case("timeout", seconds=1)
        REPORT["infrastructure_controls"] = "PASS"
    else:
        prior = Path(os.environ["RUNNER_TEMP"]) / "rh-gauss437-results"
        infra = json.loads((prior / "REPORT.json").read_text())
        acquisition = json.loads((prior / "LEAN-ACQUISITION.json").read_text())
        assert infra["infrastructure_controls"] == "PASS" and infra["worker_commit"] == os.environ["GITHUB_SHA"]
        assert acquisition["worker_commit"] == os.environ["GITHUB_SHA"]
        assert acquisition["observed_archive_sha256"] == pins["future_linux_asset"]["sha256"]
        assert all(x["empty"] for x in infra["cleanup"])
        REPORT["compiler_executable_sha256"] = hashlib.sha256((BASE / "lean" / "bin" / "lean").read_bytes()).hexdigest()
        REPORT["lake_executable_sha256"] = hashlib.sha256((BASE / "lean" / "bin" / "lake").read_bytes()).hexdigest()
        (INPUTS / ".lake").mkdir()
        (INPUTS / "lakefile.toml").write_text('name = "u03_worker_fit"\nversion = "0.0.0"\ndefaultTargets = ["FitConsumer"]\nmoreLeanArgs = ["-j", "1", "-M", "3072"]\n[[lean_lib]]\nname = "FitProvider"\n[[lean_lib]]\nname = "FitConsumer"\n')
        (INPUTS / "lean-toolchain").write_text("leanprover/lean4:v4.37.0-rc1\n")
        (INPUTS / "lake-manifest.json").write_text(json.dumps({"version":"1.3.0","packagesDir":".lake/packages","name":"u03_worker_fit","lakeDir":".lake","fixedToolchain":False,"packages":[]}))
        (INPUTS / "FitProvider.lean").write_text("namespace FitProvider\ndef workerNumber : Nat := 7\nend FitProvider\n#print axioms FitProvider.workerNumber\n")
        (INPUTS / "FitConsumer.lean").write_text("import FitProvider\ndef workerConsumer : Nat := FitProvider.workerNumber\n#print axioms workerConsumer\n")
        REPORT["fit_input_hashes"] = {p.name: hashlib.sha256(p.read_bytes()).hexdigest() for p in INPUTS.iterdir() if p.is_file()}
        run_case("lean_version")
        run_case("lean_hash")
        run_case("lake_fit")
        REPORT["core_Lake_fit"] = "PASS"
    REPORT["full_Lake_qualification"] = "PENDING_REAL_LEAN_LAKE_FIT_AND_WORK_GRAPH"
except Exception as e:
    REPORT["core_Lake_fit" if STAGE == "fit" else "infrastructure_controls"] = "BLOCKED"
    REPORT["first_blocker"] = str(e)
finally:
    REPORT["cleanup"] = []
    for unit in UNITS:
        try:
            before = systemd_properties(unit)
        except Exception as e:
            REPORT["core_Lake_fit" if STAGE == "fit" else "infrastructure_controls"] = "BLOCKED"
            REPORT["cleanup_blocker"] = "native unit state unavailable: " + str(e)
            before = {}
        subprocess.run(["sudo", "systemctl", "kill", "--kill-whom=all", "--signal=KILL", unit],
                       stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        try:
            stop = subprocess.run(["sudo", "systemctl", "stop", unit],
                                  stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=5)
            stop_exit = stop.returncode
        except Exception:
            stop_exit = None
        empty = stop_exit == 0 and bool(before)
        group = before.get("ControlGroup", "")
        if group:
            events = Path("/sys/fs/cgroup") / group.lstrip("/") / "cgroup.events"
            empty = empty and (not events.exists() or "populated 0" in events.read_text())
        REPORT["cleanup"].append({"unit": unit, "stop_exit": stop_exit,
                                  "empty": empty, "native_before_stop": before})
        if not empty:
            REPORT["core_Lake_fit" if STAGE == "fit" else "infrastructure_controls"] = "BLOCKED"
            REPORT["cleanup_blocker"] = "terminal descendants not proven empty"
        subprocess.run(["sudo", "systemctl", "reset-failed", unit],
                       stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    (ROOT / "REPORT.json").write_text(json.dumps(REPORT, indent=2, sort_keys=True))
    print(json.dumps(REPORT, sort_keys=True), flush=True)
sys.exit(0 if REPORT.get("core_Lake_fit" if STAGE == "fit" else "infrastructure_controls") == "PASS" else 1)
