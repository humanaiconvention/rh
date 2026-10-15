"""Rebuild or audit this release using only Python's standard library."""
import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess

ROOT = Path(__file__).resolve().parents[1]
MATHLIB_REV = "6015dbbfc399f4548bafd46f9560ff61595fd328"
TOOLCHAIN = "leanprover/lean4:v4.35.0"
ORIGINAL_SOURCE = "f8255264e049f39706786d6b549db81b2fb20c5d58ba9200c29003b7deef63ac"
ORIGINAL_REPORT = "8ffc07b73844870fc2775a616521f1059f286aaa61a06f1071a29444eb1918e9"
PROOF_CODE = "888238a940a04c275a3ff5396b6ce5366197fc8f5cf8a983cb1e1a05befb3507"
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
REQUIRED = {
    "RHArchitectureObstructions.physical_deficit_at_half",
    "RHArchitectureObstructions.eisenstein_prime_reciprocal_unbounded",
    "RHArchitectureObstructions.half_outside_proved_moment_range",
    "RHArchitectureObstructions.principal_euler_defect_lower_bound",
    "RHArchitectureObstructions.principal_defects_unbounded_of_prime_reciprocals",
    "RHArchitectureObstructions.principal_prime_defects_unbounded",
    "RHArchitectureObstructions.principal_all_prime_defects_not_summable",
}


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def run(args):
    completed = subprocess.run(
        [str(arg) for arg in args], cwd=ROOT, capture_output=True,
        encoding="utf-8", errors="replace", timeout=1800,
    )
    output = completed.stdout + completed.stderr
    if completed.returncode:
        raise RuntimeError(f"Command failed ({completed.returncode}): {args}\n{output}")
    return output


def lake_executable():
    found = shutil.which("lake")
    if found:
        return found
    profile = os.environ.get("USERPROFILE", str(Path.home()))
    candidate = Path(profile) / ".elan" / "bin" / ("lake.exe" if os.name == "nt" else "lake")
    if candidate.is_file():
        return str(candidate)
    raise RuntimeError("Lake is unavailable; install Elan and the pinned toolchain")


def source_code(text):
    # This frozen source has no nested comments or string literals in proofs.
    # The digest fixes its proof tokens; this is not a general Lean parser.
    code = re.sub(r"/\-.*?\-/", "", text, flags=re.S)
    return re.sub(r"--[^\n]*", "", code)


def accepted_declarations(code):
    # Normalize only the public module wrapper added for Lean 4.35 packaging.
    # The statements, definitions, and proof bodies remain byte-token equivalent.
    code = re.sub(r"\Amodule\s+", "", code, count=1)
    code = code.replace("public import Mathlib", "import Mathlib", 1)
    code = code.replace("@[expose] public section", "", 1)
    return " ".join(code.split())


def configuration():
    for name in ("lean-toolchain", "lake-toolchain"):
        if (ROOT / name).read_text(encoding="utf-8").strip() != TOOLCHAIN:
            raise RuntimeError(f"Incorrect compiler pin in {name}")
    lakefile = (ROOT / "lakefile.lean").read_text(encoding="utf-8")
    if MATHLIB_REV not in lakefile or "https://github.com/leanprover-community/mathlib4.git" not in lakefile:
        raise RuntimeError("The mathlib dependency pin is missing")
    manifest = json.loads((ROOT / "lake-manifest.json").read_text(encoding="utf-8"))
    packages = {entry["name"]: entry for entry in manifest["packages"]}
    mathlib = packages.get("mathlib", {})
    if mathlib.get("type") != "git" or mathlib.get("rev") != MATHLIB_REV:
        raise RuntimeError("The Lake manifest does not lock the intended mathlib commit")
    if mathlib.get("inputRev") != MATHLIB_REV:
        raise RuntimeError("The mathlib input revision is not immutable")
    for package in packages.values():
        if package.get("type") != "git" or not re.fullmatch(r"[0-9a-f]{40}", package.get("rev", "")):
            raise RuntimeError("A dependency is not locked to a Git commit")
    revision = run(["git", "-C", ROOT / ".lake" / "packages" / "mathlib", "rev-parse", "HEAD"]).strip()
    if revision != MATHLIB_REV:
        raise RuntimeError("The materialized mathlib revision differs")
    return manifest


def audit_axioms(output):
    if "sorryAx" in output or re.search(r"\b(?:error|warning):", output):
        raise RuntimeError("The compiler audit contains an error, warning, or proof admission")
    records = {}
    for name, raw in re.findall(
            r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", output, re.S):
        axioms = {word.strip() for word in raw.split(",") if word.strip()}
        if not axioms <= ALLOWED_AXIOMS:
            raise RuntimeError(f"Unapproved axiom dependencies for {name}: {sorted(axioms)}")
        records[name] = sorted(axioms)
    if not REQUIRED <= records.keys():
        raise RuntimeError("Compiler output is missing a required theorem audit")
    return records


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--audit-log", type=Path,
                        help="Audit output already produced by a successful direct compiler run")
    parser.add_argument("--record", action="store_true",
                        help="Write the release verification report after a successful local rebuild")
    args = parser.parse_args()
    if args.record and args.audit_log:
        parser.error("--record requires this script to execute its own build and compiler checks")
    source = ROOT / "Obstructions.lean"
    source_hash = sha256(source)
    code = source_code(source.read_text(encoding="utf-8"))
    if re.search(r"\b(sorry|admit|axiom|unsafe|native_decide)\b", code):
        raise RuntimeError("A proof admission, custom axiom, or trust shortcut is present")
    proof_hash = hashlib.sha256(accepted_declarations(code).encode("utf-8")).hexdigest()
    if proof_hash != PROOF_CODE:
        raise RuntimeError("Proof tokens differ from the accepted implementation for this release")
    original_path = ROOT / "provenance" / "VERIFICATION.original.json"
    if sha256(original_path) != ORIGINAL_REPORT:
        raise RuntimeError("The preserved verification report has changed")
    original = json.loads(original_path.read_text(encoding="utf-8"))
    if original["source_sha256"] != ORIGINAL_SOURCE:
        raise RuntimeError("Unexpected original verified source")
    configuration()
    lake = lake_executable()
    version = run([lake, "env", "lean", "--version"]).strip()
    if "version 4.35.0," not in version:
        raise RuntimeError("The active compiler is not Lean 4.35.0")
    if args.audit_log:
        build_output = None
        output = args.audit_log.read_text(encoding="utf-8")
    else:
        print("Building the pinned project...", flush=True)
        build_output = run([lake, "build", "--wfail"])
        print("Running the standalone compiler and axiom audit...", flush=True)
        output = run([lake, "env", "lean", "Obstructions.lean"])
    records = audit_axioms(output)
    if sha256(source) != source_hash:
        raise RuntimeError("The source changed during verification")
    if args.record:
        log = f"LEAN VERSION\n{version}\n\nBUILD\n{build_output}"
        log += f"\nDIRECT COMPILER AND AXIOM AUDIT\n{output}"
        (ROOT / "VERIFICATION.log").write_text(log, encoding="utf-8", newline="\n")
        report = {
            "result": "pass",
            "artifact_version": "0.1.0",
            "verified_at_utc": datetime.now(timezone.utc).isoformat(),
            "lean": version,
            "mathlib_commit": MATHLIB_REV,
            "source_sha256": source_hash,
            "proof_code_sha256": proof_hash,
            "compiler_exit_code": 0,
            "build_exit_code": 0,
            "proof_admissions": 0,
            "extra_mathematical_axioms": [],
            "audited_theorems": records,
            "euler_strip": "1/2 < Re(x) <= 2/3",
            "local_norm_cutoff": 64,
            "full_prime_family_outside_finite_exclusion": True,
            "scope": original["scope"],
            "provenance": {
                "original_source_sha256": ORIGINAL_SOURCE,
                "original_report": "provenance/VERIFICATION.original.json",
                "original_report_sha256": ORIGINAL_REPORT,
                "public_source_changes": "Explanatory comments and public module wrapper; statements and proof bodies preserved",
            },
            "lake_manifest_sha256": sha256(ROOT / "lake-manifest.json"),
            "log_sha256": sha256(ROOT / "VERIFICATION.log"),
        }
        (ROOT / "VERIFICATION.json").write_text(
            json.dumps(report, indent=2) + "\n", encoding="utf-8", newline="\n")
    else:
        report = json.loads((ROOT / "VERIFICATION.json").read_text(encoding="utf-8"))
        if report.get("result") != "pass" or report.get("source_sha256") != source_hash:
            raise RuntimeError("The saved report does not certify these exact source bytes")
        if report.get("audited_theorems") != records or report.get("mathlib_commit") != MATHLIB_REV:
            raise RuntimeError("The current theorem audit differs from the saved report")
        if sha256(ROOT / "VERIFICATION.log") != report.get("log_sha256"):
            raise RuntimeError("The saved compiler log has changed")
        if sha256(ROOT / "lake-manifest.json") != report.get("lake_manifest_sha256"):
            raise RuntimeError("The saved dependency manifest has changed")
    print(json.dumps({
        "result": "pass",
        "source_sha256": source_hash,
        "proof_admissions": 0,
        "extra_mathematical_axioms": [],
        "theorems_audited": len(records),
    }, indent=2))


if __name__ == "__main__":
    main()
