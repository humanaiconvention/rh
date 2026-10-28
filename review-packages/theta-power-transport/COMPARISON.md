# What the actual power-coordinate family adds

These comparisons describe the inspected statements. They are not new compiled interoperability theorems or current-upstream absence findings. The build uses package-local providers listed in [DEPS.json](DEPS.json), not sources from sibling package directories.

## Generic coordinate comparison

The [generic coordinate package](../coordinate-single-crossing/README.md) assumes an AE-measurable real coordinate ψ on an arbitrary measurable base, integrability of d and ψd, zero signed mass, and `(ψ-a)d ≥ 0` almost everywhere. It proves weighted Lipschitz-composition integrability, the coordinate-moment bound and its sharp unit-budget equivalence. It does not identify a particular density or prove an application's crossing and moment inputs.

This package sets the measure to Lebesgue measure restricted to `(0,∞)`, uses the actual normalized density difference d = p-q, and takes ψ(u)=u^k. It discharges the generic hypotheses from the actual normalization, crossing and moment providers. Its weighted-integrability theorem also proves integrability against each density separately, enabling the exact difference of two integrals in the final API.

## Actual theta/Macdonald cumulative and moment order

The [theta/Macdonald package](../theta-macdonald/README.md) establishes the actual source normalization, unique density crossing, strict cumulative order and strict positive natural-power moment order, together with supporting integrability and tail results.

Strict power-moment order supplies Δ_k > 0 for k > 0. It does not by itself state a universal bound over arbitrary Lipschitz functions of the power coordinate. This package adds that bound and its exact sharp-budget characterization, using the identity test in coordinate space. The power-coordinate family retains its complete source definitions and does not replace them with a finite theta prefix or numerical samples.

The result is quantified over natural k, rather than certified only at selected exponents. It is not a numerical estimate uniform in k, a real-exponent extension, or a claim that u ↦ φ(u^k) is Lipschitz in u.
