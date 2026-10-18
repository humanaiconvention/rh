import RhAnchoredConvolutionFormula001
import RhAnchoredShiftAE001

noncomputable section
open MeasureTheory Set Filter
open scoped Topology Interval BigOperators
namespace RhAnchored

def orientation (x : ℝ) : ℝ := if x < 0 then -1 else 1

lemma orientation_measurable : Measurable orientation :=
  measurable_const.piecewise measurableSet_Iio measurable_const

lemma orientation_norm (x : ℝ) : ‖orientation x‖ = 1 := by
  by_cases hx : x < 0 <;> simp [orientation, hx]

def signedExponentialOperator (A ν : ℝ) (w : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ u in interval A, orientation (t-u)*Real.exp (-ν*|t-u|)*w u

theorem signedExponentialOperator_eq_flux {A t : ℝ} (hA : 0 < A) {v : ℝ → ℝ}
    (hv : MemLp v 2 (physicalMeasure A)) (ν : ℝ) (ht : t ∈ interval A) :
    signedExponentialOperator A ν (primitive A v) t =
    exponentialFlux A ν (primitive A v) t := by
  have hw : IntervalIntegrable (primitive A v) volume (-A) A :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith : -A ≤ A)).2
      (primitive_integrableOn hv)
  have hE : IntervalIntegrable
      (fun u => Real.exp (-ν*|t-u|)*primitive A v u) volume (-A) A :=
    hw.continuousOn_mul (by fun_prop)
  have hS : IntervalIntegrable
      (fun u => orientation (t-u)*Real.exp (-ν*|t-u|)*primitive A v u) volume (-A) A := by
    apply hE.mono_fun
    · exact (((orientation_measurable.comp (by fun_prop : Measurable (fun u : ℝ => t-u))).mul
        (by fun_prop : Measurable (fun u : ℝ => Real.exp (-ν*|t-u|)))).mul
        (primitive_measurable hv)).aestronglyMeasurable
    · exact Eventually.of_forall (fun u => by simp only [norm_mul, orientation_norm, one_mul]; rfl)
  have hleft : IntervalIntegrable
      (fun u => orientation (t-u)*Real.exp (-ν*|t-u|)*primitive A v u) volume (-A) t := by
    apply hS.mono_set
    rw [uIcc_of_le ht.1, uIcc_of_le (by linarith : -A ≤ A)]
    intro u hu
    exact ⟨hu.1, hu.2.trans ht.2⟩
  have hright : IntervalIntegrable
      (fun u => orientation (t-u)*Real.exp (-ν*|t-u|)*primitive A v u) volume t A := by
    apply hS.mono_set
    rw [uIcc_of_le ht.2, uIcc_of_le (by linarith : -A ≤ A)]
    intro u hu
    exact ⟨ht.1.trans hu.1, hu.2⟩
  have hleft_value :
      (∫ u in (-A)..t, orientation (t-u)*Real.exp (-ν*|t-u|)*primitive A v u) =
      Real.exp (-ν*t)*weightedCumulative A ν (primitive A v) t := by
    unfold weightedCumulative
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr_uIoo
    intro u hu
    rw [uIoo_of_le ht.1] at hu
    have huI : u ∈ interval A := ⟨hu.1.le, hu.2.le.trans ht.2⟩
    simp only [zeroExtension_eq huI, orientation,
      ite_eq_right (not_lt.mpr (sub_nonneg.mpr hu.2.le)),
      abs_of_pos (sub_pos.mpr hu.2), one_mul]
    rw [show -ν*(t-u)= -ν*t+ν*u by ring, Real.exp_add]
    ring
  have hright_value :
      (∫ u in t..A, orientation (t-u)*Real.exp (-ν*|t-u|)*primitive A v u) =
      -Real.exp (ν*t)*(weightedCumulative A (-ν) (primitive A v) A-
        weightedCumulative A (-ν) (primitive A v) t) := by
    rw [weightedCumulative_difference hA hv]
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr_uIoo
    intro u hu
    rw [uIoo_of_le ht.2] at hu
    have huI : u ∈ interval A := ⟨ht.1.trans hu.1.le, hu.2.le⟩
    simp only [zeroExtension_eq huI, orientation, ite_eq_left (sub_neg.mpr hu.1),
      abs_of_neg (sub_neg.mpr hu.1)]
    rw [show -ν* -(t-u)=ν*t+(-ν)*u by ring, Real.exp_add]
    ring
  unfold signedExponentialOperator exponentialFlux
  rw [integral_window_eq_interval hA,
    ← intervalIntegral.integral_add_adjacent_intervals hleft hright,
    hleft_value, hright_value]
  ring

lemma signedExponentialOperator_ac {A : ℝ} (hA : 0 < A) {v : ℝ → ℝ}
    (hv : MemLp v 2 (physicalMeasure A)) (ν : ℝ) :
    AbsolutelyContinuousOnInterval (signedExponentialOperator A ν (primitive A v)) (-A) A := by
  apply (exponentialFlux_ac hA hv ν).congr
  intro t ht
  rw [uIcc_of_le (by linarith : -A ≤ A)] at ht
  exact (signedExponentialOperator_eq_flux hA hv ν ht).symm

theorem signedExponentialOperator_hasDerivAt {A t : ℝ} (hA : 0 < A) {v : ℝ → ℝ}
    (hv : MemLp v 2 (physicalMeasure A)) (ν : ℝ)
    (ht : t ∈ Ioo (-A) A) (ht0 : t ≠ 0) :
    HasDerivAt (signedExponentialOperator A ν (primitive A v))
      (2*primitive A v t-ν*exponentialOperator A ν (primitive A v) t) t := by
  have hd := exponentialFlux_native_hasDerivAt hA hv ν ⟨ht.1.le, ht.2.le⟩ ht0
    (ne_of_gt ht.1) (ne_of_lt ht.2)
  apply hd.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds ht.1 ht.2] with u hu
  exact signedExponentialOperator_eq_flux hA hv ν ⟨hu.1.le, hu.2.le⟩

theorem signedExponentialOperator_ae_deriv {A : ℝ} (hA : 0 < A) {v : ℝ → ℝ}
    (hv : MemLp v 2 (physicalMeasure A)) (ν : ℝ) :
    ∀ᵐ t ∂physicalMeasure A,
      deriv (signedExponentialOperator A ν (primitive A v)) t =
      2*primitive A v t-ν*exponentialOperator A ν (primitive A v) t := by
  unfold physicalMeasure
  rw [ae_restrict_iff' (show MeasurableSet (interval A) from measurableSet_Icc)]
  filter_upwards [ae_ne_const (-A), ae_ne_const A, ae_ne_const 0] with t htL htR ht0 htI
  exact (signedExponentialOperator_hasDerivAt hA hv ν
    ⟨lt_of_le_of_ne htI.1 (Ne.symm htL), lt_of_le_of_ne htI.2 htR⟩ ht0).deriv

end RhAnchored
#print axioms RhAnchored.signedExponentialOperator_eq_flux
#print axioms RhAnchored.signedExponentialOperator_ae_deriv
