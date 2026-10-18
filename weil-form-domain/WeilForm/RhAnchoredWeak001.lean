import RhAnchoredPrimitive001

/-!
Weak integration by parts with the actual jump mass retained.
The tests are absolutely continuous on both closed halves. Their common value
at zero makes the jump correction explicit. Smooth test functions are included.
-/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology Interval
namespace RhAnchored

lemma ae_deriv_leftPrimitive {A : ℝ} {v : ℝ → ℝ}
    (hv : MemLp v 2 (physicalMeasure A)) :
    ∀ᵐ t, t ∈ uIcc (-A) 0 →
      deriv (leftPrimitive A v) t = zeroExtension A v t := by
  filter_upwards [(zeroExtension_integrable hv).intervalIntegrable.ae_hasDerivAt_integral
    (a := -A) (b := 0)] with t ht hmem
  exact (ht hmem (-A) (by simp)).deriv

lemma ae_deriv_rightPrimitive {A : ℝ} {v : ℝ → ℝ}
    (hv : MemLp v 2 (physicalMeasure A)) :
    ∀ᵐ t, t ∈ uIcc 0 A →
      deriv (rightPrimitive A v) t = zeroExtension A v t := by
  filter_upwards [(zeroExtension_integrable hv).intervalIntegrable.ae_hasDerivAt_integral
    (a := 0) (b := A)] with t ht hmem
  exact (ht hmem A (by simp)).deriv

lemma primitive_test_left_integrable {A : ℝ} (hA : 0 < A) {v φ : ℝ → ℝ}
    (hv : MemLp v 2 (physicalMeasure A))
    (hφ : AbsolutelyContinuousOnInterval φ (-A) 0) :
    IntervalIntegrable (fun t => primitive A v t * deriv φ t) volume (-A) 0 := by
  apply (hφ.intervalIntegrable_deriv.continuousOn_mul (leftPrimitive_ac hA hv).continuousOn).congr_uIoo
  intro t ht
  rw [uIoo_of_lt (by linarith : -A < (0 : ℝ))] at ht
  simp only [primitive_eq_left v ht.2]

lemma primitive_test_right_integrable {A : ℝ} (hA : 0 < A) {v φ : ℝ → ℝ}
    (hv : MemLp v 2 (physicalMeasure A))
    (hφ : AbsolutelyContinuousOnInterval φ 0 A) :
    IntervalIntegrable (fun t => primitive A v t * deriv φ t) volume 0 A := by
  apply (hφ.intervalIntegrable_deriv.continuousOn_mul (rightPrimitive_ac hA hv).continuousOn).congr_uIoo
  intro t ht
  rw [uIoo_of_lt hA] at ht
  simp only [primitive_eq_right v ht.1]

lemma primitive_parts_left {A : ℝ} (hA : 0 < A) {v φ : ℝ → ℝ}
    (hv : MemLp v 2 (physicalMeasure A))
    (hφ : AbsolutelyContinuousOnInterval φ (-A) 0) :
    (∫ t in (-A)..0, zeroExtension A v t * φ t) =
    leftPrimitive A v 0 * φ 0 - ∫ t in (-A)..0, primitive A v t * deriv φ t := by
  have hparts := (leftPrimitive_ac hA hv).integral_deriv_mul_eq_sub hφ
  have hderiv : (∫ t in (-A)..0, deriv (leftPrimitive A v) t * φ t) =
      ∫ t in (-A)..0, zeroExtension A v t * φ t := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [ae_deriv_leftPrimitive hv] with t ht hmem
    rw [ht (uIoc_subset_uIcc hmem)]
  have hw : (∫ t in (-A)..0, leftPrimitive A v t * deriv φ t) =
      ∫ t in (-A)..0, primitive A v t * deriv φ t := by
    apply intervalIntegral.integral_congr_uIoo
    intro t ht
    rw [uIoo_of_lt (by linarith : -A < (0 : ℝ))] at ht
    simp only [primitive_eq_left v ht.2]
  rw [intervalIntegral.integral_add
    ((leftPrimitive_ac hA hv).intervalIntegrable_deriv.mul_continuousOn hφ.continuousOn)
    (hφ.intervalIntegrable_deriv.continuousOn_mul (leftPrimitive_ac hA hv).continuousOn),
    hderiv, hw] at hparts
  have hend : leftPrimitive A v (-A) = 0 := by simp [leftPrimitive]
  rw [hend] at hparts
  linarith

lemma primitive_parts_right {A : ℝ} (hA : 0 < A) {v φ : ℝ → ℝ}
    (hv : MemLp v 2 (physicalMeasure A))
    (hφ : AbsolutelyContinuousOnInterval φ 0 A) :
    (∫ t in 0..A, zeroExtension A v t * φ t) =
    -rightPrimitive A v 0 * φ 0 - ∫ t in 0..A, primitive A v t * deriv φ t := by
  have hparts := (rightPrimitive_ac hA hv).integral_deriv_mul_eq_sub hφ
  have hderiv : (∫ t in 0..A, deriv (rightPrimitive A v) t * φ t) =
      ∫ t in 0..A, zeroExtension A v t * φ t := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [ae_deriv_rightPrimitive hv] with t ht hmem
    rw [ht (uIoc_subset_uIcc hmem)]
  have hw : (∫ t in 0..A, rightPrimitive A v t * deriv φ t) =
      ∫ t in 0..A, primitive A v t * deriv φ t := by
    apply intervalIntegral.integral_congr_uIoo
    intro t ht
    rw [uIoo_of_lt hA] at ht
    simp only [primitive_eq_right v ht.1]
  rw [intervalIntegral.integral_add
    ((rightPrimitive_ac hA hv).intervalIntegrable_deriv.mul_continuousOn hφ.continuousOn)
    (hφ.intervalIntegrable_deriv.continuousOn_mul (rightPrimitive_ac hA hv).continuousOn),
    hderiv, hw] at hparts
  have hend : rightPrimitive A v A = 0 := by simp [rightPrimitive]
  rw [hend] at hparts
  linarith

theorem primitive_weak_derivative_halves {A : ℝ} (hA : 0 < A) {v φ : ℝ → ℝ}
    (hv : MemLp v 2 (physicalMeasure A))
    (hφL : AbsolutelyContinuousOnInterval φ (-A) 0)
    (hφR : AbsolutelyContinuousOnInterval φ 0 A) :
    (∫ t in (-A)..A, primitive A v t * deriv φ t) =
    -(∫ t in (-A)..A, zeroExtension A v t * φ t) + totalMass A v * φ 0 := by
  have hl := primitive_parts_left hA hv hφL
  have hr := primitive_parts_right hA hv hφR
  have hw := intervalIntegral.integral_add_adjacent_intervals
    (primitive_test_left_integrable hA hv hφL) (primitive_test_right_integrable hA hv hφR)
  have hf := intervalIntegral.integral_add_adjacent_intervals
    ((zeroExtension_integrable hv).intervalIntegrable.mul_continuousOn hφL.continuousOn)
    ((zeroExtension_integrable hv).intervalIntegrable.mul_continuousOn hφR.continuousOn)
  have hj := primitive_jump hA hv
  have hc : (leftPrimitive A v 0-rightPrimitive A v 0)*φ 0=totalMass A v*φ 0 := by
    congr 1
    linarith
  nlinarith

theorem primitive_weak_derivative {A : ℝ} (hA : 0 < A) {v φ : ℝ → ℝ}
    (hv : MemLp v 2 (physicalMeasure A))
    (hφ : AbsolutelyContinuousOnInterval φ (-A) A) :
    (∫ t in (-A)..A, primitive A v t * deriv φ t) =
    -(∫ t in (-A)..A, zeroExtension A v t * φ t) + totalMass A v * φ 0 := by
  apply primitive_weak_derivative_halves hA hv
  · apply hφ.mono
    rw [uIcc_of_le (by linarith : -A ≤ (0 : ℝ)), uIcc_of_le (by linarith : -A ≤ A)]
    intro t ht
    exact ⟨ht.1, le_trans ht.2 hA.le⟩
  · apply hφ.mono
    rw [uIcc_of_le hA.le, uIcc_of_le (by linarith : -A ≤ A)]
    intro t ht
    exact ⟨le_trans (by linarith : -A ≤ (0 : ℝ)) ht.1, ht.2⟩

theorem primitive_parts_anchored {A : ℝ} (hA : 0 < A) {v φ : ℝ → ℝ}
    (hv : MemLp v 2 (physicalMeasure A))
    (hφ : AbsolutelyContinuousOnInterval φ (-A) A) (hzero : φ 0 = 0) :
    (∫ t in (-A)..A, zeroExtension A v t * φ t) =
    -(∫ t in (-A)..A, primitive A v t * deriv φ t) := by
  have h := primitive_weak_derivative hA hv hφ
  rw [hzero] at h
  linarith

end RhAnchored
#print axioms RhAnchored.primitive_weak_derivative
#print axioms RhAnchored.primitive_parts_anchored
