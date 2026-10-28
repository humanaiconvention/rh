import Mathlib.Analysis.Polynomial.Basic

/-!
# Polynomial logarithmic degree

A nonzero real polynomial has logarithmic growth index equal to its
natural degree. This generic finite-product rigidity lemma has no
Riemann-hypothesis, analytic-source, or multiplier-sequence assumptions.
-/

open Filter Asymptotics
open scoped Topology

namespace Polynomial

/-- The logarithmic growth index of a nonzero real polynomial is its degree.
The absolute value includes negative leading coefficients, and nonzero
constant polynomials have index zero. -/
theorem tendsto_log_abs_eval_div_log (p : Polynomial ℝ) (hp : p ≠ 0) :
    Tendsto (fun x : ℝ => Real.log |p.eval x| / Real.log x)
      atTop (𝓝 (p.natDegree : ℝ)) := by
  obtain ⟨φ, hφ, heq⟩ := p.isEquivalent_atTop_lead.exists_eq_mul
  have hlog : Tendsto (fun x => Real.log (φ x)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.log_one] using
      (Real.continuousAt_log (one_ne_zero : (1 : ℝ) ≠ 0)).tendsto.comp hφ
  have hrem : Tendsto
      (fun x => (Real.log (φ x) + Real.log p.leadingCoeff) / Real.log x)
      atTop (𝓝 0) :=
    (hlog.add_const _).div_atTop Real.tendsto_log_atTop
  have hlim : Tendsto
      (fun x => (p.natDegree : ℝ) +
        (Real.log (φ x) + Real.log p.leadingCoeff) / Real.log x)
      atTop (𝓝 (p.natDegree : ℝ)) := by
    simpa using hrem.const_add (p.natDegree : ℝ)
  refine (tendsto_congr' ?_).2 hlim
  filter_upwards [heq, hφ.eventually_const_lt (zero_lt_one : (0 : ℝ) < 1),
    eventually_gt_atTop (1 : ℝ)] with x hx hφx hx1
  have hx0 : x ≠ 0 := (zero_lt_one.trans hx1).ne'
  have hlc : p.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hp
  change p.eval x = φ x * (p.leadingCoeff * x ^ p.natDegree) at hx
  rw [Real.log_abs, hx,
    Real.log_mul hφx.ne' (mul_ne_zero hlc (pow_ne_zero _ hx0)),
    Real.log_mul hlc (pow_ne_zero _ hx0), Real.log_pow]
  simp only [add_div, mul_div_cancel_right₀ _ (Real.log_pos hx1).ne']
  ac_rfl

/-- A polynomial logarithmic growth index cannot be outside the
nonnegative integers. This excludes any proposed nonintegral limit
without assuming a polynomial's degree or eventual sign in advance. -/
theorem not_tendsto_log_abs_eval_div_log_of_not_nat
    (p : Polynomial ℝ) (hp : p ≠ 0) {a : ℝ}
    (ha : ∀ n : ℕ, a ≠ (n : ℝ)) :
    ¬ Tendsto (fun x : ℝ => Real.log |p.eval x| / Real.log x) atTop (𝓝 a) := by
  intro h
  exact ha p.natDegree (tendsto_nhds_unique h (p.tendsto_log_abs_eval_div_log hp))

end Polynomial

#print axioms Polynomial.tendsto_log_abs_eval_div_log
#print axioms Polynomial.not_tendsto_log_abs_eval_div_log_of_not_nat
