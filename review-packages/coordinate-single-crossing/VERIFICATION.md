# Verification status

## Historical accepted source

The unchanged [CoordinateSingleCrossing.lean](CoordinateSingleCrossing.lean) has SHA-256

`787b8a61607d1735517e09390cdad4dc1e05847abd262fcc595fa78d75e8c19a`.

Saved acceptance records a successful module check at **2026-10-23T21:25:50.813936+00:00**, using Lean **4.36.0-rc1** and Mathlib **c85646e3ac7d3ca39468f114b2d95d62e1611533**. The actual saved terminal reports cover all five declarations in [THEOREM-STATEMENTS.md](THEOREM-STATEMENTS.md). Each report lists only `propext`, `Classical.choice`, and `Quot.sound`.

The source imports exactly:

- `Mathlib.MeasureTheory.Integral.Bochner.Basic`
- `Mathlib.Topology.MetricSpace.Lipschitz`
- `Mathlib.Tactic.Ring`

It imports no local provider, theta/Macdonald density module, cumulative API package, or RH theorem. The five terminal `#print axioms` commands remain in the source. [EVIDENCE.json](EVIDENCE.json) records the curated historical evidence; [DEPENDENCIES.json](DEPENDENCIES.json) records the pinned dependency boundary.

## Extracted package not freshly replayed

No new compilation, dependency build, standalone replay, importing-consumer check, or current-upstream compatibility check was performed for this packet. The extracted root configuration and lock have not been accepted by Lake. Build guidance in [BUILD.md](BUILD.md) is a proposed standard route, not evidence that it ran or authorization to bypass execution gates.

The historical source acceptance does not prove that any particular application satisfies the integrability, measurability, zero-mass or sign hypotheses. Actual theta/Macdonald coordinate applications are separate and are not included in this package. No RH estimate, strict moment inequality, probability normalization, or constructed transport coupling is supplied.

Static source identification and review are distinct from a fresh compiler transcript and from external independent review. No new current-upstream absence or novelty determination is claimed.
