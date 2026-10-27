# Gauss digamma difference integral

This package formalizes Gauss’s integral formula for the difference of two digamma values. The digamma function is the logarithmic derivative of the Gamma function:

$$
\psi(z)=\frac{\Gamma'(z)}{\Gamma(z)}.
$$

For a positive real number $a$ and a complex number $z$ with $\operatorname{Re}(z)>0$, the package proves

$$
\psi(z)-\psi(a)=\int_0^\infty
\frac{e^{-at}-e^{-zt}}{1-e^{-t}}\,dt.
$$

A separate theorem proves that the displayed complex-valued integrand is Lebesgue integrable on the positive half-line. Convergence is part of the result, rather than an assumption.

## How the proof works

The two terms in the numerator stay together near zero. Each exponential approaches one, so their constant parts cancel. The quotient approaches $z-a$. When $z=a$, the numerator is identically zero.

This resembles measuring the relative motion of two boats in the same current. Subtracting their motions removes the shared drift. Here, subtraction removes the shared constant term before division.

The formal proof uses a Beta-function difference in which this cancellation is preserved, followed by an exponential change of variables. The positive real parts of the parameters control the tail of the integral.

The identity is classical. The contribution of this package is its formal implementation, including the convergence argument.

## Formal results and verification

The two principal declarations in [DigammaGauss.lean](DigammaGauss.lean) are `DigammaGauss.digamma_difference_exp` and `DigammaGauss.gauss_integrable_exp`. [Exact statements and supporting API](THEOREM-STATEMENTS.md) retain the real reference parameter and complex right-half-plane argument.

These exact source bytes have saved passing checks with **Lean 4.36.0-rc1** and **Mathlib c85646e3ac7d3ca39468f114b2d95d62e1611533**. Twenty-three saved terminal axiom reports use only `propext`, `Classical.choice`, and `Quot.sound`. The source contains 39 public lemmas/theorems and six definitions; the report count is not a separate audit print for every helper. [Verification and evidence](VERIFICATION.md).

**The newly assembled standalone package has not been built or replayed.** Its root lock is a statically checked proposal. [Build prerequisites](BUILD.md), [human review](HUMAN-REVIEW.md).

Preparation was AI-assisted. Exact historical model identities remain unverified; human understanding, rights review and release approval are pending. [Provenance](PROVENANCE.md), [attribution](ATTRIBUTION.md), [notice status](LICENSE-STATUS.md). The [API and prior-review note](API-NOTES.md) records dated upstream evidence without claiming a current absence of overlap.
