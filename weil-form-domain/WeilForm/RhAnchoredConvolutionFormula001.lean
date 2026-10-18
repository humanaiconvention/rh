import RhAnchoredConvolution001

/-!
Exact finite-window convolution formulas. The absolute-value kernel is split
at u=t before integration; no derivative is passed through its cusp.
-/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology Interval BigOperators
namespace RhAnchored

lemma integral_window_eq_interval {A : ℝ} (hA : 0 < A) (f : ℝ → ℝ) :
    (∫ t in interval A, f t) = ∫ t in (-A)..A, f t := by
  rw [intervalIntegral.integral_of_le (by linarith : -A ≤ A)]
  exact integral_Icc_eq_integral_Ioc

lemma weightedCumulative_difference {A : ℝ} (hA : 0 < A) {v : ℝ → ℝ}
    (hv : MemLp v 2 (physicalMeasure A)) (ν t : ℝ) :
    weightedCumulative A ν (primitive A v) A-weightedCumulative A ν (primitive A v) t =
    ∫ u in t..A, zeroExtension A (fun u => Real.exp (ν*u)*primitive A v u) u := by
  unfold weightedCumulative
  exact intervalIntegral.integral_interval_sub_left
    (weighted_primitive_integrable hA hv (by fun_prop)).intervalIntegrable
    (weighted_primitive_integrable hA hv (by fun_prop)).intervalIntegrable

theorem exponentialOperator_eq_energyFormula {A t : ℝ} (hA : 0 < A) {v : ℝ → ℝ}
    (hv : MemLp v 2 (physicalMeasure A)) (ν : ℝ) (ht : t ∈ interval A) :
    exponentialOperator A ν (primitive A v) t =
    exponentialEnergyFormula A ν (primitive A v) t := by
  have hw : IntervalIntegrable (primitive A v) volume (-A) A :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith : -A ≤ A)).2
      (primitive_integrableOn hv)
  have hfull : IntervalIntegrable
      (fun u => Real.exp (-ν*|t-u|)*primitive A v u) volume (-A) A :=
    hw.continuousOn_mul (by fun_prop)
  have hleft : IntervalIntegrable
      (fun u => Real.exp (-ν*|t-u|)*primitive A v u) volume (-A) t := by
    apply hfull.mono_set
    rw [uIcc_of_le ht.1, uIcc_of_le (by linarith : -A ≤ A)]
    intro u hu
    exact ⟨hu.1, hu.2.trans ht.2⟩
  have hright : IntervalIntegrable
      (fun u => Real.exp (-ν*|t-u|)*primitive A v u) volume t A := by
    apply hfull.mono_set
    rw [uIcc_of_le ht.2, uIcc_of_le (by linarith : -A ≤ A)]
    intro u hu
    exact ⟨ht.1.trans hu.1, hu.2⟩
  have hleft_value : (∫ u in (-A)..t, Real.exp (-ν*|t-u|)*primitive A v u) =
      Real.exp (-ν*t)*weightedCumulative A ν (primitive A v) t := by
    unfold weightedCumulative
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr_uIoo
    intro u hu
    rw [uIoo_of_le ht.1] at hu
    have huI : u ∈ interval A := ⟨hu.1.le, hu.2.le.trans ht.2⟩
    simp only [zeroExtension_eq huI, abs_of_pos (sub_pos.mpr hu.2)]
    rw [show -ν*(t-u)=-ν*t+ν*u by ring, Real.exp_add]
    ring
  have hright_value : (∫ u in t..A, Real.exp (-ν*|t-u|)*primitive A v u) =
      Real.exp (ν*t)*(weightedCumulative A (-ν) (primitive A v) A-
        weightedCumulative A (-ν) (primitive A v) t) := by
    rw [weightedCumulative_difference hA hv]
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr_uIoo
    intro u hu
    rw [uIoo_of_le ht.2] at hu
    have huI : u ∈ interval A := ⟨ht.1.trans hu.1.le, hu.2.le⟩
    simp only [zeroExtension_eq huI, abs_of_neg (sub_neg.mpr hu.1)]
    rw [show -ν* -(t-u)=ν*t+(-ν)*u by ring, Real.exp_add]
    ring
  unfold exponentialOperator exponentialEnergyFormula
  rw [integral_window_eq_interval hA,
    ← intervalIntegral.integral_add_adjacent_intervals hleft hright,
    hleft_value, hright_value]

theorem exponentialFlux_native_hasDerivAt {A t : ℝ} (hA : 0 < A) {v : ℝ → ℝ}
    (hv : MemLp v 2 (physicalMeasure A)) (ν : ℝ) (ht : t ∈ interval A)
    (ht0 : t ≠ 0) (htL : t ≠ -A) (htR : t ≠ A) :
    HasDerivAt (exponentialFlux A ν (primitive A v))
      (2*primitive A v t-ν*exponentialOperator A ν (primitive A v) t) t := by
  simpa only [zeroExtension_eq ht, ← exponentialOperator_eq_energyFormula hA hv ν ht] using
    exponentialFlux_hasDerivAt hA hv ν ht0 htL htR

end RhAnchored
#print axioms RhAnchored.exponentialOperator_eq_energyFormula
#print axioms RhAnchored.exponentialFlux_native_hasDerivAt
