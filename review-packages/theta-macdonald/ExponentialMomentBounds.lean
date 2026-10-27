import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Tactic

noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace ExponentialMoment

theorem quadratic_exp_integrable :
    IntegrableOn (fun t : ℝ => t^2*Real.exp (-t)) (Ioi (0 : ℝ)) := by
  simpa only [Real.rpow_two, Real.rpow_one] using
    (integrableOn_rpow_mul_exp_neg_rpow (s := 2) (p := 1)
      (by norm_num) (by norm_num))

theorem weighted_integrable {f : ℝ → ℝ} {A : ℝ}
    (hf : IntegrableOn f (Ioi (0 : ℝ)))
    (hb : ∀ t : ℝ, 0 ≤ t → ‖f t‖ ≤ A*Real.exp (-t)) :
    IntegrableOn (fun t : ℝ => t^2*f t) (Ioi (0 : ℝ)) := by
  have hm : AEStronglyMeasurable (fun t : ℝ => t^2*f t)
      (volume.restrict (Ioi (0 : ℝ))) :=
    (by fun_prop : Continuous (fun t : ℝ => t^2)).aestronglyMeasurable.mul
      hf.aestronglyMeasurable
  apply (quadratic_exp_integrable.const_mul A).mono' hm
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg t)]
  calc
    t^2*‖f t‖ ≤ t^2*(A*Real.exp (-t)) :=
      mul_le_mul_of_nonneg_left (hb t ht.le) (sq_nonneg t)
    _ = A*(t^2*Real.exp (-t)) := by ring

theorem tail_bound {f : ℝ → ℝ} {A : ℝ}
    (hb : ∀ t : ℝ, 0 ≤ t → ‖f t‖ ≤ A*Real.exp (-t))
    {u : ℝ} (hu : 0 ≤ u) :
    ‖∫ t in Ioi u, f t‖ ≤ A*Real.exp (-u) := by
  calc
    _ ≤ ∫ t in Ioi u, A*Real.exp (-t) :=
      norm_integral_le_of_norm_le ((integrableOn_exp_neg_Ioi u).const_mul A) (by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        exact hb t (hu.trans ht.le))
    _ = A*Real.exp (-u) := by
      rw [integral_const_mul, integral_exp_neg_Ioi]

theorem quadratic_exp_half_bound (t : ℝ) (ht : 0 ≤ t) :
    t^2*Real.exp (-t) ≤ 8*Real.exp (-t/2) := by
  have hp := Real.pow_div_factorial_le_exp (t/2) (by linarith : 0 ≤ t/2) 2
  norm_num at hp
  have hh : t^2 ≤ 8*Real.exp (t/2) := by nlinarith
  have h := mul_le_mul_of_nonneg_right hh (Real.exp_pos (-t)).le
  calc
    _ ≤ (8*Real.exp (t/2))*Real.exp (-t) := h
    _ = _ := by rw [mul_assoc, ← Real.exp_add]; congr 2 <;> ring

theorem weighted_tail_bound {f : ℝ → ℝ} {A : ℝ} (hA : 0 ≤ A)
    (hb : ∀ t : ℝ, 0 ≤ t → ‖f t‖ ≤ A*Real.exp (-t))
    {u : ℝ} (hu : 0 ≤ u) :
    ‖∫ t in Ioi u, t^2*f t‖ ≤ 16*A*Real.exp (-u/2) := by
  have he := integrableOn_exp_mul_Ioi (a := -(1/2 : ℝ)) (by norm_num) u
  calc
    _ ≤ ∫ t in Ioi u, (8*A)*Real.exp (-(1/2 : ℝ)*t) :=
      norm_integral_le_of_norm_le (he.const_mul (8*A)) (by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg t)]
        calc
          _ ≤ t^2*(A*Real.exp (-t)) :=
            mul_le_mul_of_nonneg_left (hb t (hu.trans ht.le)) (sq_nonneg t)
          _ = A*(t^2*Real.exp (-t)) := by ring
          _ ≤ A*(8*Real.exp (-t/2)) :=
            mul_le_mul_of_nonneg_left (quadratic_exp_half_bound t (hu.trans ht.le)) hA
          _ = _ := by rw [show -t/2 = -(1/2 : ℝ)*t by ring]; ring)
    _ = _ := by
      rw [integral_const_mul, integral_exp_mul_Ioi (by norm_num : -(1/2 : ℝ)<0)]
      rw [show -(1/2 : ℝ)*u = -u/2 by ring]
      ring

theorem quadratic_boundary_vanishes {g : ℝ → ℝ} {A : ℝ}
    (hb : ∀ u : ℝ, 0 ≤ u → ‖g u‖ ≤ A*Real.exp (-u)) :
    Tendsto (fun u : ℝ => u^2*g u) atTop (𝓝 0) := by
  apply squeeze_zero_norm' (a := fun u : ℝ => A*(u^2*Real.exp (-u))) (by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with u hu
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg u)]
    exact (mul_le_mul_of_nonneg_left (hb u hu) (sq_nonneg u)).trans_eq (by ring))
  simpa only [mul_zero] using
    (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 2).const_mul A

end ExponentialMoment
#print axioms ExponentialMoment.weighted_integrable
#print axioms ExponentialMoment.tail_bound
#print axioms ExponentialMoment.weighted_tail_bound
#print axioms ExponentialMoment.quadratic_boundary_vanishes
