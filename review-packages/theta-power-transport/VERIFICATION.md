# Verification status

## Historical accepted module

The unchanged [ThetaPowerCoordinate.lean](ThetaPowerCoordinate.lean) has SHA-256

`a5e85b183a811014614980446012fb7b0bbb178b8333a28a3c2de739b9b7fee1`.

Saved acceptance records a successful module check at **2026-10-25T18:37:08.215233+00:00**, using Lean **4.36.0-rc1** and Mathlib **c85646e3ac7d3ca39468f114b2d95d62e1611533**. Actual saved terminal reports cover all seven declarations in [THEOREM-STATEMENTS.md](THEOREM-STATEMENTS.md); each lists only `propext`, `Classical.choice`, and `Quot.sound`.

The source imports exactly `CoordinateSingleCrossing` and `ThetaMomentOrder`. The historical check reused accepted generic and actual-source provider objects. The actual module discharges the generic comparison's measurability, integrability, zero-mass and crossing hypotheses using those providers. This acceptance is stronger than compilation of a conditional comparison alone.

[EVIDENCE.json](EVIDENCE.json) records the curated acceptance boundary. [DEPS.json](DEPS.json) identifies the package-local sources and pinned dependencies, with their verification scopes. Historical reuse of accepted providers is not a new replay of their complete source closure.

## Extracted configuration and replay

The package includes its local provider sources for inspection and a proposed standard build route. Its new configuration and lock have not been accepted by Lake. A fresh standalone build and fresh importing-consumer replay are **NOT RUN**. No new compiler, dependency build, provider replay or current-upstream compatibility check occurred during this preparation. See [BUILD.md](BUILD.md).

The accepted family concerns the actual defined densities and natural-power coordinates under the exact displayed test assumptions. It does not assert a numerical bound uniform in the exponent or Lipschitzness of the composed test in physical u. No new current-upstream overlap determination, mathematical novelty review or external independent review is claimed.
