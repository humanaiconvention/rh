# Derivatives of scalar exponential generating functions

This package formalizes a coefficient rule for repeated differentiation of a complex power series.

An exponential generating function writes each coefficient with a factorial denominator:

$$
f(z)=\sum_{n\ge0}\frac{c_nz^n}{n!}.
$$

If this series represents $f$ on an open ball centered at zero, then every finite derivative order $k$ has the expansion

$$
f^{(k)}(z)=\sum_{n\ge0}\frac{c_{n+k}z^n}{n!}
$$

on the same ball.

## How the rule works

Differentiation multiplies the coefficient of $z^n$ by $n$. The factorial denominator absorbs that factor, leaving the next coefficient in the sequence. Repeating the operation shifts the sequence by $k$ places.

The coefficient sequence resembles a numbered flight checklist. Differentiation advances the starting position while preserving the format of the remaining entries.

The theorem assumes an existing power-series representation. Its contribution is a compact scalar interface to Mathlib’s differentiation machinery, with the original radius retained.

## Formal result and verification

The sole public declaration in [IteratedDerivOfScalars.lean](IteratedDerivOfScalars.lean) is `HasFPowerSeriesOnBall.iteratedDeriv_ofScalars`. It applies to complex functions and coefficients, at center zero, for every natural derivative order. The [exact statement](THEOREM-STATEMENTS.md) retains the `HasFPowerSeriesOnBall` premise and the same `r : ENNReal`; it does not merely assume a pointwise assigned sum or claim a maximal convergence radius.

These exact source bytes have saved passing checks with **Lean 4.36.0-rc1** and **Mathlib c85646e3ac7d3ca39468f114b2d95d62e1611533**. The one saved terminal axiom report lists only `propext`, `Classical.choice`, and `Quot.sound`. The row definition and derivative-step theorem remain private. [Verification and evidence](VERIFICATION.md).

**The newly assembled standalone package has not been built or replayed.** Its root lock is a statically checked proposal. [Build prerequisites](BUILD.md), [human review](HUMAN-REVIEW.md). The unchanged source's older uncompiled-candidate header records an earlier stage, not a denial of the later saved acceptance; [history and provenance](PROVENANCE.md) explain the distinction.

Preparation was AI-assisted. Exact historical model identities remain unverified; human understanding, rights review and release approval remain pending. [Attribution](ATTRIBUTION.md), [notice status](LICENSE-STATUS.md), [API fit](API-NOTES.md).
