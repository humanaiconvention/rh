"""Compile the source-only domain/Schur package against existing pinned dependencies.
No downloads, installations, original research directories or local proof caches.
Run from any directory; output is a NEW .verification/run-* directory.
"""
from pathlib import Path
import argparse, ctypes, datetime, hashlib, json, os, re, subprocess, sys, time

ROOT=Path(__file__).resolve().parent
PIN="6015dbbfc399f4548bafd46f9560ff61595fd328"
ALLOWED={"propext","Classical.choice","Quot.sound"}
sha=lambda p: hashlib.sha256(p.read_bytes()).hexdigest()

def compile_bounded(cmd, cwd, env, output, timeout):
    # The Lean heap flag is portable. The additional Windows working-set
    # guard is fail-closed; other systems retain the explicit heap boundary.
    proc=subprocess.Popen(cmd,cwd=cwd,env=env,stdout=output,stderr=subprocess.STDOUT)
    peak=0;fatal=None;started=time.monotonic()
    if os.name=="nt":
        class PMC(ctypes.Structure):
            _fields_=[("cb",ctypes.c_ulong),("PageFaultCount",ctypes.c_ulong)]+[(n,ctypes.c_size_t) for n in
                ["PeakWorkingSetSize","WorkingSetSize","QuotaPeakPagedPoolUsage","QuotaPagedPoolUsage",
                 "QuotaPeakNonPagedPoolUsage","QuotaNonPagedPoolUsage","PagefileUsage","PeakPagefileUsage","PrivateUsage"]]
        ps=ctypes.WinDLL("psapi",use_last_error=True)
        ps.GetProcessMemoryInfo.argtypes=[ctypes.c_void_p,ctypes.POINTER(PMC),ctypes.c_ulong]
        ps.GetProcessMemoryInfo.restype=ctypes.c_int
    while proc.poll() is None:
        if os.name=="nt":
            q=PMC();q.cb=ctypes.sizeof(q)
            if not ps.GetProcessMemoryInfo(int(proc._handle),ctypes.byref(q),q.cb):
                fatal="Working-set monitor failed: "+str(ctypes.get_last_error());proc.kill();break
            peak=max(peak,q.PeakWorkingSetSize)
            if peak>int(2.9*1024**3):
                fatal="Proactive working-set stop before the 3GiB limit";proc.kill();break
        if time.monotonic()-started>timeout:
            fatal="Per-module timeout";proc.kill();break
        time.sleep(.1)
    return proc.wait(),fatal,peak

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--lean", required=True, type=Path, help="Existing Lean 4.35.0 executable")
    ap.add_argument("--packages", required=True, type=Path, help="Existing .lake/packages directory")
    ap.add_argument("--timeout", type=float, default=1800)
    ap.add_argument("--verify-only", action="store_true", help="Check release/dependency hashes and import graph without compiling")
    a=ap.parse_args()
    lean=a.lean.resolve(); packages=a.packages.resolve()
    if not lean.is_file() or not packages.is_dir(): raise SystemExit("Missing existing toolchain/dependencies")
    version=subprocess.check_output([str(lean),"--version"],text=True)
    if "version 4.35.0," not in version: raise SystemExit("Lean version must be 4.35.0")
    expected=json.loads((ROOT/"SOURCE-HASHES.json").read_text(encoding="utf-8"))
    for rel,want in expected.items():
        f=(ROOT/rel).resolve()
        if not f.is_relative_to(ROOT) or not f.is_file() or sha(f)!=want:
            raise SystemExit("Release file hash/path mismatch: "+rel)
    release=json.loads((ROOT/"REPLAY-MANIFEST.json").read_text(encoding="utf-8"))
    pins=json.loads((ROOT/"lake-manifest.json").read_text(encoding="utf-8"))["packages"]
    expected_pins={r["name"]:r["rev"] for r in release["pinned_packages"]}
    if {r["name"]:r["rev"] for r in pins}!=expected_pins:
        raise SystemExit("Dependency pins differ from the release manifest")
    genv=os.environ.copy();genv["GIT_OPTIONAL_LOCKS"]="0"
    bins=[]
    for row in pins:
        name=row["name"]
        if name!=Path(name).name or row["type"]!="git": raise SystemExit("Unexpected dependency entry")
        checkout=packages/name
        head=subprocess.check_output(["git","-C",str(checkout),"rev-parse","HEAD"],text=True,env=genv).strip()
        if head!=row["rev"]: raise SystemExit("Dependency revision mismatch: "+name)
        dirty=subprocess.run(["git","-C",str(checkout),"diff","--quiet","HEAD","--"],env=genv)
        if dirty.returncode!=0: raise SystemExit("Tracked dependency source differs from pin: "+name)
        binary=checkout/".lake/build/lib/lean"
        if binary.is_dir(): bins.append(binary)
    got=expected_pins.get("mathlib")
    if got!=PIN: raise SystemExit("mathlib release pin differs from required revision")
    external={r["module"]:r["binary_sha256"] for r in release["package_entry_boundaries"]}
    for name,want in external.items():
        hits=[b.joinpath(*name.split(".")).with_suffix(".olean") for b in bins]
        hits=[f for f in hits if f.is_file()]
        if len(hits)!=1 or sha(hits[0])!=want:
            raise SystemExit("Missing, ambiguous or changed pinned package entry binary: "+name)
    sources={p.stem:p for p in (ROOT/"WeilForm").glob("*.lean")}
    wanted={k for k in expected if k.startswith("WeilForm/") and k.endswith(".lean")}
    actual={p.relative_to(ROOT).as_posix() for p in sources.values()}
    if actual!=wanted: raise SystemExit("Source set differs from SOURCE-HASHES.json")
    for p in sources.values():
        rel=p.relative_to(ROOT).as_posix()
        if sha(p)!=expected[rel]: raise SystemExit("Source hash mismatch: "+rel)
        if re.search(r"\bsorry\b|\bnative_decide\b|(?m:^\s*(?:axiom|opaque)\b)",p.read_text(encoding="utf-8")):
            raise SystemExit("Disallowed source token: "+rel)
    expected_prints={n:re.findall(r"(?m)^#print axioms\s+([A-Za-z0-9_.]+)",p.read_text(encoding="utf-8")) for n,p in sources.items()}
    dependencies={n:re.findall(r"(?m)^\s*import\s+([A-Za-z_][A-Za-z0-9_.]*)",p.read_text(encoding="utf-8")) for n,p in sources.items()}
    for n,imports in dependencies.items():
        for dependency in imports:
            if dependency not in sources and dependency not in external:
                raise SystemExit("Unlisted external import: "+n+" -> "+dependency)
    order=[]; state={}
    def visit(n):
        if state.get(n)==1: raise SystemExit("Cyclic source dependency: "+n)
        if state.get(n)==2:return
        state[n]=1
        for d in dependencies[n]:
            if d in sources:visit(d)
        state[n]=2;order.append(n)
    for n in sorted(sources):visit(n)
    if a.verify_only:
        print(f"PASS: release hashes, pinned dependencies, {len(external)} package boundaries and {len(order)} source imports; no proof compilation requested")
        return
    stamp=datetime.datetime.now(datetime.timezone.utc).strftime("%Y%m%dT%H%M%S%fZ")
    out=ROOT/".verification"/("run-"+stamp);out.mkdir(parents=True,exist_ok=False)
    lib=out/"Lean";logs=out/"Logs";lib.mkdir();logs.mkdir()
    env=os.environ.copy();env["LEAN_PATH"]=os.pathsep.join(map(str,[lib]+bins))
    results={"lean_version":version.strip(),"lean_sha256":sha(lean),"mathlib_revision":got,
        "scope":"Fresh local source compilation. Existing pinned package binaries are reused; this is not an imported-environment kernel replay or a toolchain rebuild.",
        "package_entry_count":len(external),"pinned_packages":expected_pins,
        "heap_limit_MiB":3072,"thread_limit":2,"modules":[],"passed":False}
    def save(): (out/"receipt.json").write_text(json.dumps(results,indent=2)+"\n")
    save()
    for i,n in enumerate(order,1):
        obj=lib/(n+".olean");log=logs/(n+".log");start=time.monotonic();fatal=None
        want=expected[sources[n].relative_to(ROOT).as_posix()]
        if sha(sources[n])!=want: raise SystemExit("Source changed before compile: "+n)
        with log.open("x",encoding="utf-8") as h:
            code,fatal,peak=compile_bounded([str(lean),"-j","2","-M","3072","-o",str(obj),str(sources[n])],
                ROOT/"WeilForm",env,h,a.timeout)
        text=log.read_text(encoding="utf-8")
        axioms=[[x.strip() for x in s.split(",") if x.strip()] for s in re.findall(r"depends on axioms:\s*\[([^\]]*)\]",text,re.S)]
        bad=sorted({x for xs in axioms for x in xs if x not in ALLOWED})
        shown=re.findall(r"'([^']+)' (?:depends on axioms:|does not depend on any axioms)",text)
        if sorted(shown)!=sorted(expected_prints[n]): fatal="Terminal axiom-output names/count mismatch"
        if sha(sources[n])!=want: fatal="Source changed during compile"
        ok=code==0 and not fatal and not bad and "sorryAx" not in text and obj.is_file()
        results["modules"].append({"module":n,"source_sha256":sha(sources[n]),
            "object_sha256":sha(obj) if obj.is_file() else None,"log_sha256":sha(log),
            "axiom_lists":axioms,"printed_terminals":shown,"unexpected_axioms":bad,"exit_code":code,"fatal":fatal,
            "elapsed_seconds":round(time.monotonic()-start,3),"Windows_peak_working_set_bytes":peak if os.name=="nt" else None,"passed":ok})
        save(); print(f"{i}/{len(order)} {n}: {'PASS' if ok else 'FAIL'}",flush=True)
        if not ok: raise SystemExit("Stopped at "+n+"; inspect "+str(log))
    for rel,want in expected.items():
        if sha(ROOT/rel)!=want: raise SystemExit("Release file changed during replay: "+rel)
    results["passed"]=True;save();print("PASS: all source modules; receipt: "+str(out/"receipt.json"))

if __name__=="__main__":main()
