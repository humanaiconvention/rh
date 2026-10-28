# Pinned replay proposal; not executed

The two unchanged sources have separate historical acceptance recorded in [EVIDENCE.json](EVIDENCE.json) and [FINITE-CELL-EVIDENCE.json](FINITE-CELL-EVIDENCE.json). This extracted project, its manually assembled root lock and the new two-library configuration have not been built or accepted by Lake. No fresh combined downstream import has been checked. The recipe is a reviewable target, not an admitted runner or completion forecast.

## Exact inputs

- Use a clean copy of this package directory without inherited outputs or machine-local providers.
- Toolchain: `leanprover/lean4:v4.35.0`.
- Mathlib: `6015dbbfc399f4548bafd46f9560ff61595fd328`; the full declared project package set is in [DEPENDENCIES.json](DEPENDENCIES.json).
- Review `lakefile.toml`, `lean-toolchain` and `lake-manifest.json`. Exact `rev` values are fixed commits; branch-like `inputRev` metadata is not an instruction to update them.
- Materialize/authenticate the exact dependencies through a separately approved standard route. Configuration, setup, cache and dependency builds are separate work; no artifact readiness or producer closure is asserted.
- Review and neutralize unintended provider-path/toolchain overrides in the later isolated environment. No present environment setting has been changed.

## Intended source and consumer checks

After legitimate provisioning and process/resource admission, the intended source target is:

```text
lake build BlockSignCount FiniteCellCount
```

Both source files are flat in this directory, with their original module names. Each is declared as a separate `lean_lib` and both are proposed default targets. Neither imports the other, and neither has a custom local provider. The retained dependency revisions and portable lock are unchanged. The combined configuration is an uncompiled proposal, not a replay of either historical project.

Each source contains its saved terminal `#print axioms` commands. A later fresh importing consumer must import both exact modules and check all seven declarations below. It is not supplied as an already compiled wrapper.

```lean
import BlockSignCount
import FiniteCellCount
#check BlockSignCount.roots_of_disjoint_sign_changes
#print axioms BlockSignCount.roots_of_disjoint_sign_changes
#check BlockSignCount.roots_of_robust_margins
#print axioms BlockSignCount.roots_of_robust_margins
#check BlockSignCount.exact_block_counts
#print axioms BlockSignCount.exact_block_counts
#check RhCountingAudit.prefixCount
#check RhCountingAudit.interleaved_prefix_bounds
#print axioms RhCountingAudit.interleaved_prefix_bounds
#check RhCountingAudit.common_cells_prefix_discrepancy
#print axioms RhCountingAudit.common_cells_prefix_discrepancy
#check RhCountingAudit.roots_eq_of_distinct_witnesses
#print axioms RhCountingAudit.roots_eq_of_distinct_witnesses
#check RhCountingAudit.roots_eq_of_ordered_cell_witnesses
#print axioms RhCountingAudit.roots_eq_of_ordered_cell_witnesses
```

Record the exact source/configuration/lock fingerprints, dependency provenance, actual process accounting, logs and output identity. Require each report to remain within `propext`, `Classical.choice`, and `Quot.sound`. Reject admissions, numerical oracles, accidental private providers or changed hypotheses. A successful source build alone does not certify the importing consumer or a version port.

## Resource and acceptance boundary

The existing project limits remain: one concurrent compiler, two Lean threads, 3072 MiB Lean heap, owned working-set stop 3113851289 bytes, private/job cap 10737418240 bytes, 1 GiB physical and commit reserves, and at most four owned active processes. The two per-process flags in the proposed Lake file do not enforce concurrency, ownership or the other limits. No special scheduler, resource probe, supervisor or bypass is introduced here.

Do not assume one outer Lake command is one compiler launch. Establish supported admission and a bounded budget separately before any run; setup and provisioning are unpriced here. If the normal route is unavailable, preserve the blocker instead of retrying a denied action or extending custom infrastructure.

The companion retains its historically deprecated `Mathlib.Data.Real.Basic` import. Its saved compiler suggested `Mathlib.Basic.Real.Basic`; no import was changed here because that would create a different, unverified source. Preserve the recorded 4.35 baseline rather than inferring compatibility with another Lean/Mathlib version.

Open replay checks: root-lock acceptance without drift; clean two-target source build; actual declaration/type and transitive-axiom reports; fresh combined importer. These were not run for this snapshot. Static semantic and source-identity review is recorded separately from replay. Human API/editorial/rights review and present-upstream fit remain open.
