# Cumulative bounds for Lipschitz tests

Let μ be a measure on ℝ and d a real-valued density. Suppose d and x ↦ x d(x) are μ-integrable and the total signed mass is zero. Its inclusive cumulative function is

$$
C(t)=\int_{(-\infty,t]} d(x)\,d\mu(x).
$$

The formal results show that C is measurable and Lebesgue integrable, and that every real 1-Lipschitz function w satisfies

$$
\left|\int_{\mathbb R} w(x)d(x)\,d\mu(x)\right|
\leq \int_{\mathbb R}|C(t)|\,dt.
$$

The weighted test is integrable under these hypotheses. A 1-Lipschitz test attains the right-hand side exactly, so this cumulative integral is the sharp test budget. The final theorem characterizes that budget by an equivalence for every real B.

The proof constructs an attaining test as the anchored primitive of minus the sign of C. Zero total mass removes the additive constant in a Lipschitz test. A finite positive carrier is used internally for the signed Fubini argument; no finiteness or sigma-finiteness assumption is imposed on the original measure μ.

This is classical one-dimensional cumulative/Lipschitz duality. The useful contribution here is a formal API that includes test integrability, a genuine attainer, and the original-measure hypotheses. It does not establish an arithmetic estimate or a result about the Riemann Hypothesis.

## Verification boundary

[Cumulative.lean](Cumulative.lean) is the unchanged four-contract source with saved successful acceptance under Lean **4.36.0-rc1** and Mathlib **c85646e3ac7d3ca39468f114b2d95d62e1611533**. The four saved terminal axiom reports list only `propext`, `Classical.choice`, and `Quot.sound`.

This review package has not received a fresh standalone build or importing-consumer replay. See [exact statements](THEOREM-STATEMENTS.md), [verification scope](VERIFICATION.md), [evidence](EVIDENCE.json), [dependencies](DEPENDENCIES.json), and [replay instructions](BUILD.md). API placement, current-upstream overlap, attribution and release approval remain review questions; see [attribution](ATTRIBUTION.md).
