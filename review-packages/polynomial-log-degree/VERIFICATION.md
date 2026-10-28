# Verification status

The exact source [PolynomialLogDegree.lean](PolynomialLogDegree.lean) has SHA-256
`32df1efdd90ff90b2d266cdce0d5ddc3117c2118c9c0bedcb6dcad05fdf8f098`.
It is copied byte-identically from the historically accepted source.

The saved successful default build used Lean `leanprover/lean4:v4.35.0` and
Mathlib revision `6015dbbfc399f4548bafd46f9560ff61595fd328`. It completed
successfully on 22 October 2026 in 15.672 seconds. The saved terminal reports are:

| Declaration | Reported transitive axioms |
|---|---|
| `Polynomial.tendsto_log_abs_eval_div_log` | `propext`, `Classical.choice`, `Quot.sound` |
| `Polynomial.not_tendsto_log_abs_eval_div_log_of_not_nat` | `propext`, `Classical.choice`, `Quot.sound` |

The source retains both terminal `#print axioms` commands. Acceptance concerns
the precise statements in [API.md](API.md), not an application to any particular
analytic source. The earlier failed elaboration attempt, including temporary
error-recovery reports, is rejected and supplies no accepted proof evidence.

The [evidence summary](EVIDENCE.json) records the historical acceptance without
exporting raw runtime logs or private archive paths. No compiler, dependency
import or replay ran while preparing this package. A standalone package build,
Lean 4.36 compatibility replay and clean downstream replay are all **NOT RUN**.

Read [BUILD.md](BUILD.md) and [DEPENDENCIES.json](DEPENDENCIES.json) with those
limits: build guidance and dependency metadata do not themselves constitute
verification. Existing overlap observations are dated and pinned, not a fresh
current-upstream duplicate/absence determination. External independent review
is not claimed.
