# Polynomial logarithmic degree

For a nonzero real polynomial, `log |p(x)| / log x` tends to its natural degree
as `x` tends to positive infinity. Consequently, it cannot tend to a real number
outside the nonnegative integers. This package presents two Lean convenience
lemmas for that classical deduction.

The proof starts with Mathlib's existing leading-term asymptotic equivalence
`Polynomial.isEquivalent_atTop_lead`. Logarithm identities separate the leading
power from a factor tending to one, and ordinary limit rules finish the argument.
Absolute value includes negative leading coefficients; nonzero constants have
limit zero. Finitely many polynomial roots do not affect the eventual statement,
and the denominator is handled on the eventual set `x > 1`.

[API.md](API.md) gives the exact two exports and their hypotheses.
[PolynomialLogDegree.lean](PolynomialLogDegree.lean) is the unchanged accepted
source. It imports one Mathlib module and no local provider. The result is
generic polynomial growth rigidity; no particular analytic source, multiplier
classification or RH application is certified here.

[Verification](VERIFICATION.md) records historical Lean 4.35.0 acceptance.
Standalone, Lean 4.36 and downstream replays have not run. See also the
[evidence summary](EVIDENCE.json), [dependencies](DEPENDENCIES.json) and
[build guidance](BUILD.md).

This is a small convenience-API proposal rather than a new mathematical theorem
or standalone research-manuscript claim. Its best library placement, contribution
notices and compatibility remain review questions; [ATTRIBUTION.md](ATTRIBUTION.md)
states those boundaries. No current-upstream absence claim is made.
