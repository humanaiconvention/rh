# Relationship to the cumulative and theta/Macdonald packages

These comparisons describe the inspected theorem statements. They are not compiled interoperability results, reduction theorems, or a current-upstream novelty assessment.

## Cumulative/Lipschitz duality

The [cumulative/Lipschitz package](../cumulative-lipschitz/README.md) works with an arbitrary zero-mass signed density on the real line. Under its integrability and first-moment hypotheses, it obtains the sharp Lipschitz budget ∫|C(t)| dt and constructs an attaining test. It does not assume a single crossing.

This coordinate package works on an arbitrary measurable base α with a prescribed real coordinate ψ. Its additional AE sign condition is `(ψ-a)d ≥ 0`. The resulting sharp unit-Lipschitz budget is the coordinate moment ∫ψd, attained by the identity on coordinate space. It does not construct a cumulative function, pushforward measure or optimal coupling. Neither interface should be presented as proving the other under unchanged hypotheses.

## Strict single-crossing and moment order

The [theta/Macdonald package](../theta-macdonald/README.md) contains several different interfaces:

- `CumulativeSplit` proves finite/tail bookkeeping on the positive real half-line and strict negative prefixes from an integrable, zero-mass real function with explicit strict signs below and above a crossing.
- `MonotoneMomentOrder` proves strict weighted integral order for two equal-mass functions on that half-line, with the required weighted integrability, monotone weight and strict increase above the crossing. Its weights need not be Lipschitz.
- `ThetaCumulativeOrder` instantiates crossing and normalization facts for the actual theta and Macdonald densities to obtain strict cumulative order.

This package instead proves a non-strict absolute bound for arbitrary Lipschitz functions of an AE-measurable coordinate. It neither supplies the strict crossing and weighted-integrability inputs of those results nor certifies their actual density formulas. Conversely, the named strict-prefix and monotone-order contracts do not state the arbitrary-base Lipschitz-coordinate budget interface given here.

Actual theta/Macdonald power-coordinate applications are separate work and are not included or reverified in this packet. No claim about their current acceptance status follows from this comparison.
