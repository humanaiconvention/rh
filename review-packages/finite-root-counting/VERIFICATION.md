# Verification status

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

No compiler, dependency import or replay ran while preparing this review package.
The following remain **NOT RUN**:

- a standalone build of this extracted package;
- a Lean 4.36 compatibility port or replay;
- a clean downstream replay from the public package.

The [dependency record](DEPENDENCIES.json) and [build guidance](BUILD.md) must be
read with that distinction. A proposed build route is not a completed build.
The historical overlap review was dated and pinned; no current-upstream
duplicate/absence determination or external independent review is asserted.
