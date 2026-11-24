"""Remote Linux preflight. Infrastructure controls, never a proof verdict.

Deliberately stronger four-TASK cap, including threads. Its ability to fit Lake
is a separate control, not assumed from the original four-process budget.
"""
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import time

ROOT = Path(os.environ["RUNNER_TEMP"]) / "rh-gauss437-results"
ROOT.mkdir(exist_ok=False)
BASE = Path("/tmp") / ("rh-gauss437-" + os.environ["GITHUB_RUN_ID"])
BASE.mkdir(mode=0o755, exist_ok=False)
INPUTS = BASE / "input"
INPUTS.mkdir(mode=0o755)
shutil.copyfile(Path(__file__).with_name("fixture.py"), INPUTS / "fixture.py")
(INPUTS / "read-only.txt").write_text("frozen control input\n")
SENTINEL = BASE / "host-only-sentinel"
SENTINEL.write_text("must be absent inside the worker namespace\n")
HOST_NETNS = os.stat("/proc/self/ns/net").st_ino
REPORT = {"schema": "rh-gauss-linux-infrastructure-002",
          "claim": "NO_LEAN_OR_STRICT_PROOF_VERDICT", "cases": [],
          "gauss_build": "NOT_RUN", "strict_replay": "NOT_RUN_PENDING",
          "policy": {"tasksMax": 4, "task_vs_process": "STRONGER_THREADS_INCLUDED",
                     "memoryMax": 3113848832, "swapMax": 0,
                     "requestedPhaseLimitSec": 90, "maxLeanCompilers": "NOT_YET_QUALIFIED",
                     "controlPlane": "HOST_QUALIFIER_OUTSIDE_WORKLOAD_CGROUP_AS_IN_PRIOR_JOB_GUARD"}}
UNITS = []

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
             "RuntimeMaxUSec", "User", "NoNewPrivileges", "PrivateNetwork", "MainPID", "ControlPID"]
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
    native_runtime = max(seconds - 1, 0.25)
    command = ["sudo", "systemd-run", "--quiet", "--no-block", "--unit=" + unit,
               "--property=User=nobody", "--property=Group=nogroup",
               "--property=RemainAfterExit=yes",
               "--setenv=RH_GAUSS_FORBIDDEN_SENTINEL=must-not-reach",
               "--property=StandardOutput=append:" + str(ROOT / (case + ".stdout")),
               "--property=StandardError=append:" + str(ROOT / (case + ".stderr")),
               "--property=NoNewPrivileges=yes", "--property=TasksMax=4",
               "--property=PrivateNetwork=yes",
               "--property=MemoryMax=" + str(memory), "--property=MemorySwapMax=0",
               "--property=RuntimeMaxSec=" + str(native_runtime),
               "--property=TimeoutStartSec=0.5", "--property=TimeoutStopSec=0.25",
               "--property=KillSignal=SIGKILL", "--property=FinalKillSignal=SIGKILL",
               "--property=KillMode=control-group", "--property=OOMPolicy=kill",
               "--property=LimitCORE=0"] + sandbox
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
    assert props.get("TasksMax") == "4", "native task limit missing"
    assert props.get("MemoryMax") == str(memory), "native memory limit missing"
    assert props.get("MemorySwapMax") == "0", "native swap limit missing"
    assert props.get("User") == "nobody", "wrong execution identity"
    assert props.get("NoNewPrivileges") == "yes", "privilege gate missing"
    assert props.get("PrivateNetwork") == "yes", "outer private network missing"
    assert props.get("ControlPID") == "0", "native service control still active"
    group = props.get("ControlGroup", "")
    if group:
        events = Path("/sys/fs/cgroup") / group.lstrip("/") / "cgroup.events"
        assert not events.exists() or "populated 0" in events.read_text(), "live cgroup descendants"
    record = {"case": case, "launch_exit": p.returncode, "native": props,
              "elapsed": time.monotonic() - start}
    if case in ("isolation", "pids"):
        assert props.get("ExecMainStatus") == "0" and props.get("Result") == "success", "benign/control failed"
        control = json.loads((out / (case + ".json")).read_text())
        assert control["status"] == ("PASS" if case == "isolation" else "EXPECTED_KERNEL_REJECTION")
        record["control"] = control
    elif case == "unisolated":
        assert props.get("ExecMainStatus") == "1" and props.get("Result") == "exit-code", "wrong negative-control failure"
        assert b"ENV_LEAK" in (ROOT / (case + ".stderr")).read_bytes(), "not the intended isolation rejection"
    elif case == "memory":
        assert props.get("ExecMainStatus") != "0" and props.get("Result") == "oom-kill", "not the intended OOM rejection"
    elif case == "timeout":
        assert props.get("ExecMainStatus") != "0" and props.get("Result") == "timeout", "not the intended timeout rejection"
    record["verdict"] = "EXPECTED_RESULT"
    REPORT["cases"].append(record)

try:
    assert os.environ.get("GITHUB_REPOSITORY") == "humanaiconvention/rh"
    assert sys.platform == "linux"
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
    assert REPORT["bwrap_sha256"] == "e318903862396f96de3df57264e0158682b952fd3fb53ac23d876413e7b30f71", "bubblewrap changed from inspected candidate pin"
    REPORT["qualifier_sha256"] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    REPORT["fixture_sha256"] = hashlib.sha256((INPUTS / "fixture.py").read_bytes()).hexdigest()
    REPORT["start_available_bytes"] = available()
    run_case("isolation")
    run_case("unisolated")
    run_case("pids")
    run_case("memory", memory=128 * 1024**2)
    run_case("timeout", seconds=1)
    REPORT["infrastructure_controls"] = "PASS"
    REPORT["full_Lake_qualification"] = "PENDING_REAL_LEAN_LAKE_FIT_AND_WORK_GRAPH"
except Exception as e:
    REPORT["infrastructure_controls"] = "BLOCKED"
    REPORT["first_blocker"] = str(e)
finally:
    REPORT["cleanup"] = []
    for unit in UNITS:
        try:
            before = systemd_properties(unit)
        except Exception as e:
            REPORT["infrastructure_controls"] = "BLOCKED"
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
            REPORT["infrastructure_controls"] = "BLOCKED"
            REPORT["cleanup_blocker"] = "terminal descendants not proven empty"
        subprocess.run(["sudo", "systemctl", "reset-failed", unit],
                       stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    (ROOT / "REPORT.json").write_text(json.dumps(REPORT, indent=2, sort_keys=True))
    print(json.dumps(REPORT, sort_keys=True), flush=True)
sys.exit(0 if REPORT.get("infrastructure_controls") == "PASS" else 1)
