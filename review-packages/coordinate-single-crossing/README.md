# Signed single-crossing bounds along a coordinate

Let α be a measurable space with a measure μ, d a real-valued signed density, and ψ a real coordinate. Assume d and ψd are integrable, the total signed mass is zero, and, for some real a,

$$
(\psi(x)-a)d(x)\geq 0\qquad\text{for μ-almost every }x.
$$

The coordinate moment M = ∫ ψd dμ is then nonnegative. If ψ is AE measurable, every real K-Lipschitz function φ has an integrable weighted composition and satisfies

$$
\left|\int \phi(\psi(x))d(x)\,d\mu(x)\right|\leq K M.
$$

For unit Lipschitz tests, M is the sharp budget: the identity function on coordinate space attains it. The final theorem expresses this as an equivalence for every real proposed budget B.

The proof centers the test at a. Zero total mass removes its constant value, the Lipschitz condition controls its variation, and the signed crossing condition converts the resulting product into the nonnegative centered moment. This is a classical signed comparison argument, formalized on an arbitrary measurable base without constructing a pushforward or coupling.

The sign condition is non-strict and almost everywhere. It does not assert a unique crossing, strict moment positivity, or nondegeneracy. Zero density and constant-coordinate cases are permitted. The Lipschitz constant is a nonnegative real (`ℝ≥0`), including zero. No finite or sigma-finite ambient-measure assumption, probability normalization, or topology on α is imposed.

## Review and verification

[CoordinateSingleCrossing.lean](CoordinateSingleCrossing.lean) is the unchanged five-contract source with saved successful acceptance under Lean **4.36.0-rc1** and Mathlib **c85646e3ac7d3ca39468f114b2d95d62e1611533**. Its five saved terminal axiom reports list only `propext`, `Classical.choice`, and `Quot.sound`.

This extracted package has not received a fresh standalone build or importing-consumer replay. Its new build configuration is a proposal, not an accepted environment. See [exact types](THEOREM-STATEMENTS.md), [verification scope](VERIFICATION.md), [evidence](EVIDENCE.json), [dependencies](DEPENDENCIES.json), and [build guidance](BUILD.md).

The package presents a reusable formal interface for this classical comparison. Actual theta/Macdonald coordinate applications are separate and are not included. [COMPARISON.md](COMPARISON.md) explains the distinction from related packages; [ATTRIBUTION.md](ATTRIBUTION.md) records the open review and notice questions.
