# Exact API and hypotheses

The public declarations in namespace `Polynomial` are:

```lean
theorem tendsto_log_abs_eval_div_log (p : Polynomial ℝ) (hp : p ≠ 0) :
    Tendsto (fun x : ℝ => Real.log |p.eval x| / Real.log x)
      atTop (𝓝 (p.natDegree : ℝ))

theorem not_tendsto_log_abs_eval_div_log_of_not_nat
    (p : Polynomial ℝ) (hp : p ≠ 0) {a : ℝ}
    (ha : ∀ n : ℕ, a ≠ (n : ℝ)) :
    ¬ Tendsto (fun x : ℝ => Real.log |p.eval x| / Real.log x) atTop (𝓝 a)
```

The authoritative unchanged proof is [PolynomialLogDegree.lean](PolynomialLogDegree.lean).
The only import is `Mathlib.Analysis.Polynomial.Basic`; the leading-term input
is the existing `Polynomial.isEquivalent_atTop_lead` theorem.

`hp` is the only additional assumption in the first result. It includes nonzero
constants and negative leading coefficients. The limit is at positive infinity,
so exceptional finite roots and `x = 1` do not alter the conclusion. The second
result uses uniqueness of limits and the explicit hypothesis excluding every
natural-number value. It assumes neither a specified degree nor an eventual
polynomial sign.

There are no public helper definitions or local provider dependencies. No
source-specific asymptotic, numerical approximation or analytic application is
proved by this interface.
