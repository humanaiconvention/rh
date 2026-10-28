# Verification status: two separate historical sources

## Sign-witness and block-count source

The exact source [BlockSignCount.lean](BlockSignCount.lean) has SHA-256
`350132774fd882542e873d900a80e1cdf3a3b83b682449eaf18740092e067af7`.
It is copied byte-identically from the historically accepted source.

The saved successful default build used:

- Lean `leanprover/lean4:v4.35.0`;
- Mathlib revision `6015dbbfc399f4548bafd46f9560ff61595fd328`;
- successful compilation on 22 October 2026, elapsed 15.125 seconds.

The three terminal reports were:

| Declaration | Reported transitive axioms |
|---|---|
| `BlockSignCount.roots_of_disjoint_sign_changes` | `propext`, `Classical.choice`, `Quot.sound` |
| `BlockSignCount.roots_of_robust_margins` | `propext`, `Classical.choice`, `Quot.sound` |
| `BlockSignCount.exact_block_counts` | `propext`, `Classical.choice`, `Quot.sound` |

The source retains its three terminal `#print axioms` commands. Acceptance refers
to the exact [API hypotheses](API.md), including the nonzero polynomial, strict
sign changes, disjoint open intervals and degree budget. No source-specific
analytic premise is discharged here.

Earlier failed elaboration attempts and their temporary error-recovery reports
are excluded from acceptance. They do not supply evidence for these claims.
The public [evidence summary](EVIDENCE.json) records the accepted boundary without
exporting raw runtime logs or private archive paths.

## Ordered-prefix companion source

The unchanged [FiniteCellCount.lean](FiniteCellCount.lean) has SHA-256
`a2344f1714bb80423bf081367cfa997ba821e492e50e2f740c1849ba4088635f`.
Its separate successful build ran from 2026-10-22T17:48:35.769330Z through
2026-10-22T17:48:49.240642Z under the same Lean 4.35.0 / Mathlib revision.
The saved log contains four actual reports, each restricted to `propext`,
`Classical.choice`, and `Quot.sound`:

- `RhCountingAudit.interleaved_prefix_bounds`;
- `RhCountingAudit.common_cells_prefix_discrepancy`;
- `RhCountingAudit.roots_eq_of_distinct_witnesses`;
- `RhCountingAudit.roots_eq_of_ordered_cell_witnesses`.

One deprecation warning concerns `Mathlib.Data.Real.Basic`. It does not change
the historical successful result; the original import remains unchanged.
[Companion evidence](FINITE-CELL-EVIDENCE.json) retains the exact source, record,
log and saved-object fingerprints and the four report lines without exporting
private runtime records. The local source closure is one module with two
Mathlib imports and no custom provider. The complete two-module package closure
and declared pinned project dependencies are in [DEPENDENCIES.json](DEPENDENCIES.json).

These seven reports came from two separately accepted sources. They are not a
successful combined-project build. Static checks authenticate their copied bytes
and exact types, not a new binary-producer or per-module Mathlib import closure.

## Extracted configuration and consumer remain unverified

No compiler, dependency import or replay ran while preparing this companion.
The following remain **NOT RUN**:

- a standalone build of this extracted package;
- acceptance of the modified two-library/default-target configuration;
- a Lean 4.36 compatibility port or replay;
- a fresh consumer importing both public modules.

The [dependency record](DEPENDENCIES.json) and [build guidance](BUILD.md) must be
read with that distinction. A proposed build route is not a completed build.
The historical overlap review was dated and pinned; no current-upstream
duplicate/absence determination or external independent review is asserted.
