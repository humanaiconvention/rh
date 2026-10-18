"""Freshly compile all 227 parent-plus-supplement local modules.
No downloads or installations. Existing pinned package/toolchain binaries
are an explicit trust boundary. Output is a new .verification/run-* directory.
"""
from pathlib import Path
import argparse, ctypes, datetime, hashlib, json, os, re, subprocess, time

ROOT=Path(__file__).resolve().parent
PARENT=ROOT.parent/"weil-form-domain"
ALLOWED={"propext","Classical.choice","Quot.sound"}
PIN="6015dbbfc399f4548bafd46f9560ff61595fd328"
LIMIT=3*1024**3
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
read=lambda p:json.loads(p.read_text(encoding="utf-8"))

def source_imports(p):
    return re.findall(r"(?m)^\s*import\s+([A-Za-z_][A-Za-z0-9_.]*)",p.read_text(encoding="utf-8"))

def terminal_names(p):
    return re.findall(r"(?m)^#print axioms\s+([A-Za-z0-9_.]+)",p.read_text(encoding="utf-8"))

def distributed_files(folder):
    return {p.relative_to(folder).as_posix() for p in folder.rglob("*") if p.is_file()
        and not any(part in {".verification",".lake","__pycache__"} for part in p.relative_to(folder).parts)}

def check_hashes(folder,expected):
    if distributed_files(folder)!=set(expected)|{"SOURCE-HASHES.json"}:
        raise SystemExit("Distributed file allowlist mismatch: "+folder.name)
    for rel,want in expected.items():
        p=(folder/rel).resolve()
        if not p.is_relative_to(folder) or not p.is_file() or sha(p)!=want:
            raise SystemExit("Distributed file hash/path mismatch: "+folder.name+"/"+rel)

def compile_bounded(cmd,cwd,env,output,timeout):
    """Fail closed on monitor/cap setup errors; never relax the saved cap."""
    preexec=None
    if os.name=="nt":
        class PMC(ctypes.Structure):
            _fields_=[("cb",ctypes.c_ulong),("PageFaultCount",ctypes.c_ulong)]+[(n,ctypes.c_size_t) for n in
                ["PeakWorkingSetSize","WorkingSetSize","QuotaPeakPagedPoolUsage","QuotaPagedPoolUsage",
                 "QuotaPeakNonPagedPoolUsage","QuotaNonPagedPoolUsage","PagefileUsage","PeakPagefileUsage","PrivateUsage"]]
        ps=ctypes.WinDLL("psapi",use_last_error=True)
        ps.GetProcessMemoryInfo.argtypes=[ctypes.c_void_p,ctypes.POINTER(PMC),ctypes.c_ulong]
        ps.GetProcessMemoryInfo.restype=ctypes.c_int
    elif os.name=="posix":
        import resource
        if not hasattr(resource,"RLIMIT_AS"):
            raise SystemExit("Cannot enforce the required POSIX address-space cap")
        def set_cap():
            resource.setrlimit(resource.RLIMIT_AS,(LIMIT,LIMIT))
        preexec=set_cap
    else:
        raise SystemExit("No fail-closed memory boundary is implemented for this platform")
    proc=subprocess.Popen(cmd,cwd=cwd,env=env,stdout=output,stderr=subprocess.STDOUT,preexec_fn=preexec)
    peak=0;fatal=None;started=time.monotonic()
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
    return proc.wait(),fatal,peak if os.name=="nt" else None

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--lean",required=True,type=Path,help="Existing matching Lean4.35.0 executable")
    ap.add_argument("--packages",required=True,type=Path,help="Existing pinned .lake/packages directory")
    ap.add_argument("--timeout",type=float,default=1800)
    ap.add_argument("--verify-only",action="store_true",help="Authenticate files/imports/pins without compiling")
    a=ap.parse_args()
    if not 0<a.timeout<=1800:raise SystemExit("The per-module timeout must be in (0,1800]")
    lean=a.lean.resolve();packages=a.packages.resolve()
    if not lean.is_file() or not packages.is_dir():raise SystemExit("Missing existing toolchain/dependencies")
    expected=read(ROOT/"SOURCE-HASHES.json")
    check_hashes(ROOT,expected)
    manifest=read(ROOT/"REPLAY-MANIFEST.json")
    parent=manifest["parent"]
    if parent["git_commit"]!="46a969283f22775a7a064df297cf10f7d9caf578":
        raise SystemExit("Unexpected immutable parent commit")
    for name,key in [("SOURCE-HASHES.json","source_hashes_sha256"),
                     ("REPLAY-MANIFEST.json","replay_manifest_sha256"),
                     ("FRESH-REPLAY-RECEIPT.json","fresh_replay_receipt_sha256")]:
        if sha(PARENT/name)!=parent[key]:raise SystemExit("Parent boundary mismatch: "+name)
    parent_expected=read(PARENT/"SOURCE-HASHES.json")
    check_hashes(PARENT,parent_expected)
    base=read(PARENT/"FRESH-REPLAY-RECEIPT.json")
    if not base["passed"] or len(base["modules"])!=199:
        raise SystemExit("Missing completed immutable parent source replay")
    version=subprocess.check_output([str(lean),"--version"],text=True)
    if "version 4.35.0," not in version or sha(lean)!=manifest["toolchain"]["executable_sha256"]:
        raise SystemExit("Lean version or tested executable hash differs; authenticate a new boundary separately")
    if manifest["toolchain"]["mathlib_commit"]!=PIN:raise SystemExit("Unexpected mathlib pin")
    pins=read(PARENT/"lake-manifest.json")["packages"]
    wanted={r["name"]:(r["url"],r["rev"]) for r in manifest["pinned_packages"]}
    if {r["name"]:(r["url"],r["rev"]) for r in pins}!=wanted:
        raise SystemExit("Pinned dependency metadata mismatch")
    bins=[];genv=os.environ.copy();genv["GIT_OPTIONAL_LOCKS"]="0"
    def check_packages():
        for row in pins:
            name=row["name"]
            if name!=Path(name).name or row["type"]!="git":raise SystemExit("Unexpected package entry")
            checkout=packages/name
            head=subprocess.check_output(["git","-C",str(checkout),"rev-parse","HEAD"],text=True,env=genv).strip()
            if head!=row["rev"]:raise SystemExit("Package revision mismatch: "+name)
            if subprocess.run(["git","-C",str(checkout),"diff","--quiet","HEAD","--"],env=genv).returncode:
                raise SystemExit("Tracked package source is not clean at the pin: "+name)
    check_packages()
    for row in pins:
        b=packages/row["name"]/".lake/build/lib/lean"
        if b.is_dir():bins.append(b)
    external={r["module"]:r["binary_sha256"] for r in manifest["package_entry_boundaries"]}
    if len(external)!=80:raise SystemExit("Expected exactly 80 direct package boundaries")
    def check_binary_boundaries():
        for n,want in external.items():
            hits=[b.joinpath(*n.split(".")).with_suffix(".olean") for b in bins]
            hits=[p for p in hits if p.is_file()]
            if len(hits)!=1 or sha(hits[0])!=want:
                raise SystemExit("Missing, ambiguous or changed package binary: "+n)
    check_binary_boundaries()
    rows={r["module"]:r for r in manifest["modules"]}
    if len(rows)!=227:raise SystemExit("Expected 227 distinct local modules")
    sources={}
    for n,r in rows.items():
        folder=PARENT/"WeilForm" if r["owner"]=="published_parent" else ROOT/"WeilNullCrossing"
        p=(ROOT/r["filename"]).resolve()
        if p.parent!=folder or p.name!=n+".lean" or not p.is_file() or sha(p)!=r["source_sha256"]:
            raise SystemExit("Source hash/path mismatch: "+n)
        if source_imports(p)!=r["imports"] or terminal_names(p)!=r["terminal_declarations"]:
            raise SystemExit("Source import/terminal metadata mismatch: "+n)
        if re.search(r"\bsorry\b|\bnative_decide\b|(?m:^\s*(?:axiom|opaque)\b)",p.read_text(encoding="utf-8")):
            raise SystemExit("Disallowed source token: "+n)
        sources[n]=p
    if sum(r["owner"]=="published_parent" for r in rows.values())!=199:
        raise SystemExit("Parent source count mismatch")
    if sum(r["owner"]=="supplement" for r in rows.values())!=28:
        raise SystemExit("Supplement source count mismatch")
    actual_external={d for r in rows.values() for d in r["imports"] if d not in rows}
    if actual_external!=set(external):raise SystemExit("Direct-import allowlist mismatch")
    order=[];state={};memo={}
    def visit(n):
        if state.get(n)==1:raise SystemExit("Source import cycle: "+n)
        if state.get(n)==2:return
        state[n]=1
        for d in rows[n]["imports"]:
            if d in rows:visit(d)
        state[n]=2;order.append(n)
    def fingerprint(n):
        if n not in rows:return "package:"+n
        if n not in memo:
            r=rows[n]
            memo[n]=hashlib.sha256((r["source_sha256"]+"|"+"|".join(fingerprint(d)for d in r["imports"])).encode()).hexdigest()
        return memo[n]
    for n in sorted(rows):visit(n)
    if order!=manifest["order"]:raise SystemExit("Source topological order mismatch")
    for n in order:
        if fingerprint(n)!=rows[n]["dependency_source_fingerprint"]:
            raise SystemExit("Recursive source/import fingerprint mismatch: "+n)
    prints=sum(len(r["terminal_declarations"])for r in rows.values())
    if prints!=729:raise SystemExit("Expected 729 terminal axiom reports")
    if a.verify_only:
        print("PASS: unchanged parent 199 + supplement 28 sources, 80 package boundaries, 729 declared terminal reports; no compilation requested")
        return
    stamp=datetime.datetime.now(datetime.timezone.utc).strftime("%Y%m%dT%H%M%S%fZ")
    out=ROOT/".verification"/("run-"+stamp);out.mkdir(parents=True,exist_ok=False)
    lib=out/"Lean";logs=out/"Logs";lib.mkdir();logs.mkdir()
    env=os.environ.copy();env["LEAN_PATH"]=os.pathsep.join(map(str,[lib]+bins))
    env["PYTHONDONTWRITEBYTECODE"]="1"
    results={"scope":"Fresh source compilation of ALL 227 local modules (199 immutable parent +28 supplement) from empty local outputs. Existing pinned package/toolchain binaries are reused. This is not a toolchain rebuild, external independent review or a separate imported-environment kernel replay.",
        "passed":False,"lean_version":version.strip(),"lean_sha256":sha(lean),"mathlib_revision":PIN,
        "pinned_packages":{r["name"]:r["rev"]for r in pins},"package_entry_count":80,
        "local_source_count":227,"parent_source_count":199,"supplement_source_count":28,
        "parent_commit":parent["git_commit"],"source_manifest_sha256":sha(ROOT/"REPLAY-MANIFEST.json"),
        "source_hash_list_sha256":sha(ROOT/"SOURCE-HASHES.json"),
        "heap_limit_MiB":3072,"thread_limit":2,"per_module_timeout_seconds":a.timeout,
        "memory_boundary":"Windows monitored working-set stop before 3 GiB" if os.name=="nt" else "POSIX 3 GiB RLIMIT_AS",
        "modules":[]}
    def save():(out/"receipt.json").write_text(json.dumps(results,indent=2)+"\n",encoding="utf-8")
    save()
    for i,n in enumerate(order,1):
        source=sources[n];obj=lib/(n+".olean");log=logs/(n+".log");start=time.monotonic()
        if sha(source)!=rows[n]["source_sha256"]:raise SystemExit("Source changed before compilation: "+n)
        with log.open("x",encoding="utf-8")as handle:
            code,fatal,peak=compile_bounded([str(lean),"-j","2","-M","3072","-o",str(obj),str(source)],source.parent,env,handle,a.timeout)
        text=log.read_text(encoding="utf-8")
        axs=[[x.strip()for x in s.split(",")if x.strip()]for s in re.findall(r"depends on axioms:\s*\[([^\]]*)\]",text,re.S)]
        bad=sorted({x for xs in axs for x in xs if x not in ALLOWED})
        shown=re.findall(r"'([^']+)' (?:depends on axioms:|does not depend on any axioms)",text)
        if sorted(shown)!=sorted(rows[n]["terminal_declarations"]):fatal="Terminal axiom-output names/count mismatch"
        if sha(source)!=rows[n]["source_sha256"]:fatal="Source changed during compilation"
        ok=code==0 and fatal is None and not bad and "sorryAx"not in text and obj.is_file()
        results["modules"].append({"module":n,"owner":rows[n]["owner"],"source_sha256":sha(source),
            "object_sha256":sha(obj)if obj.is_file()else None,"log_sha256":sha(log),
            "printed_terminals":shown,"axiom_lists":axs,"unexpected_axioms":bad,
            "exit_code":code,"fatal":fatal,"elapsed_seconds":round(time.monotonic()-start,3),
            "Windows_peak_working_set_bytes":peak,"passed":ok})
        save();print(f"{i}/227 {n}: {'PASS'if ok else 'FAIL'}",flush=True)
        if not ok:raise SystemExit("Stopped at "+n+"; inspect the new private output log")
    check_hashes(ROOT,expected);check_hashes(PARENT,parent_expected)
    check_packages();check_binary_boundaries()
    if sha(lean)!=results["lean_sha256"]:raise SystemExit("Toolchain changed during compilation")
    results["terminal_report_count"]=sum(len(r["printed_terminals"])for r in results["modules"])
    results["passed"]=True;save()
    print("PASS: ALL 227 local sources freshly compiled; 729 terminal reports; receipt: "+str(out/"receipt.json"))

if __name__=="__main__":main()
