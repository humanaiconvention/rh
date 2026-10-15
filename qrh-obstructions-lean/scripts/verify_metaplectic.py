"""Compile and audit the finite conjugate-slot algebra, using the pinned project."""
import argparse
from datetime import datetime, timezone
import json
from pathlib import Path
import re

import verify as baseline

ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / "MetaplecticDictionary.lean"
REPORT = ROOT / "METAPLECTIC-VERIFICATION.json"
LOG = ROOT / "METAPLECTIC-VERIFICATION.log"
REQUIRED = {
    "MetaplecticDictionary." + name for name in (
        "omega_primitive", "omega_integral", "p_normSq", "pbar_normSq",
        "p_square", "phase_exists", "u_pbar_cube", "phase_polynomial",
        "phase_lower_bound", "survival_polynomial", "survival_bounds",
        "combined_phase_nonzero",
    )
}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--record", action="store_true",
                        help="Save a fresh compiler and axiom verification record")
    parser.add_argument("--audit-log", type=Path,
                        help="Audit output from an already successful direct compiler run")
    args = parser.parse_args()
    if args.record and args.audit_log:
        parser.error("--record executes its own build and compiler checks")
    source_hash = baseline.sha256(SOURCE)
    code = baseline.source_code(SOURCE.read_text(encoding="utf-8"))
    if re.search(r"\b(sorry|admit|axiom|unsafe|native_decide)\b", code):
        raise RuntimeError("A proof admission, custom axiom, or trust shortcut is present")
    baseline.configuration()
    lake = baseline.lake_executable()
    version = baseline.run([lake, "env", "lean", "--version"]).strip()
    if "version 4.35.0," not in version:
        raise RuntimeError("The active compiler is not Lean 4.35.0")
    if args.audit_log:
        build_output = None
        output = args.audit_log.read_text(encoding="utf-8")
    else:
        print("Building the finite algebra module without warnings...", flush=True)
        build_output = baseline.run([lake, "build", "MetaplecticDictionary", "--wfail"])
        print("Running the standalone compiler and axiom audit...", flush=True)
        output = baseline.run([lake, "env", "lean", "MetaplecticDictionary.lean"])
    if "sorryAx" in output or re.search(r"\b(?:error|warning):", output):
        raise RuntimeError("The compiler reported an error, warning, or proof admission")
    records = {}
    for name, raw in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", output, re.S):
        axioms = {item.strip() for item in raw.split(",") if item.strip()}
        if not axioms <= baseline.ALLOWED_AXIOMS:
            raise RuntimeError(f"Unapproved axiom dependencies for {name}: {sorted(axioms)}")
        records[name] = sorted(axioms)
    if not REQUIRED <= records.keys():
        raise RuntimeError("A required theorem is missing from the axiom audit")
    if baseline.sha256(SOURCE) != source_hash:
        raise RuntimeError("The source changed during verification")
    if args.record:
        LOG.write_text(
            f"LEAN VERSION\n{version}\n\nBUILD\n{build_output}"
            f"\nDIRECT COMPILER AND AXIOM AUDIT\n{output}",
            encoding="utf-8", newline="\n",
        )
        report = {
            "result": "pass",
            "verified_at_utc": datetime.now(timezone.utc).isoformat(),
            "lean": version,
            "mathlib_commit": baseline.MATHLIB_REV,
            "source": SOURCE.name,
            "source_sha256": source_hash,
            "build_exit_code": 0,
            "compiler_exit_code": 0,
            "proof_admissions": 0,
            "extra_mathematical_axioms": [],
            "audited_theorems": records,
            "scope": (
                "Exact conjugate norm-157 elements in Z[omega], unit cubic roots of "
                "conjugate(alpha)^2, their real pair polynomial, quantitative bounds, "
                "and nonvanishing. Does not certify the native Gauss-sum identification, "
                "a complete physical row value, a trace formula, or an analytic bound."
            ),
            "phase_choice": "Existential witness; the general theorem applies to every qualifying phase",
            "log_sha256": baseline.sha256(LOG),
        }
        REPORT.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8", newline="\n")
    else:
        report = json.loads(REPORT.read_text(encoding="utf-8"))
        if report.get("result") != "pass" or report.get("source_sha256") != source_hash:
            raise RuntimeError("The saved report does not certify the current source")
        if report.get("audited_theorems") != records or report.get("mathlib_commit") != baseline.MATHLIB_REV:
            raise RuntimeError("The theorem audit or dependency pin differs from the saved report")
        if baseline.sha256(LOG) != report.get("log_sha256"):
            raise RuntimeError("The saved compiler log has changed")
    print(json.dumps({"result": "pass", "source_sha256": source_hash,
                      "theorems_audited": len(records), "proof_admissions": 0,
                      "extra_mathematical_axioms": []}, indent=2))


if __name__ == "__main__":
    main()
