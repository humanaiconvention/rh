import RhNativeBumpCapacity001
import RhDilationRankL2001

/-! Actual anchored-primitive linearity and physical L2 continuity.
The bound here is a convergence estimate, not a replacement for any saved floor.
-/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology Interval
namespace RhPrimitiveApproximation
open RhAnchored

lemma zeroExtension_add (R : ℝ) (v u : ℝ → ℝ) :
    zeroExtension R (v + u) = zeroExtension R v + zeroExtension R u := by
  funext t
  by_cases ht : t ∈ interval R
  · simp [zeroExtension, ht]
  · simp [zeroExtension, ht]

lemma zeroExtension_smul (R c : ℝ) (v : ℝ → ℝ) :
    zeroExtension R (c • v) = c • zeroExtension R v := by
  funext t
  by_cases ht : t ∈ interval R
  · simp [zeroExtension, ht]
  · simp [zeroExtension, ht]

/-- This is equality of actual representatives, including their assigned zero. -/
theorem primitive_add {R : ℝ} {v u : ℝ → ℝ}
    (hv : MemLp v 2 (physicalMeasure R)) (hu : MemLp u 2 (physicalMeasure R)) :
    primitive R (v + u) = primitive R v + primitive R u := by
  funext t
  change primitive R (v + u) t = primitive R v t + primitive R u t
  by_cases ht : t < 0
  · rw [primitive_eq_left (v + u) ht, primitive_eq_left v ht, primitive_eq_left u ht]
    unfold leftPrimitive
    rw [zeroExtension_add]
    simpa only [Pi.add_apply] using intervalIntegral.integral_add
      (zeroExtension_integrable hv).intervalIntegrable
      (zeroExtension_integrable hu).intervalIntegrable
  · by_cases ht' : 0 < t
    · rw [primitive_eq_right (v + u) ht', primitive_eq_right v ht', primitive_eq_right u ht']
      unfold rightPrimitive
      rw [zeroExtension_add]
      simpa only [Pi.add_apply] using intervalIntegral.integral_add
        (zeroExtension_integrable hv).intervalIntegrable
        (zeroExtension_integrable hu).intervalIntegrable
    · simp only [primitive, ite_eq_right ht, ite_eq_right ht', add_zero]

lemma primitive_smul (R c : ℝ) (v : ℝ → ℝ) :
    primitive R (c • v) = c • primitive R v := by
  funext t
  change primitive R (c • v) t = c * primitive R v t
  by_cases ht : t < 0
  · rw [primitive_eq_left (c • v) ht, primitive_eq_left v ht]
    unfold leftPrimitive
    rw [zeroExtension_smul]
    simpa only [Pi.smul_apply, smul_eq_mul] using
      (intervalIntegral.integral_smul (a := -R) (b := t) c (zeroExtension R v))
  · by_cases ht' : 0 < t
    · rw [primitive_eq_right (c • v) ht', primitive_eq_right v ht']
      unfold rightPrimitive
      rw [zeroExtension_smul]
      simpa only [Pi.smul_apply, smul_eq_mul] using
        (intervalIntegral.integral_smul (a := R) (b := t) c (zeroExtension R v))
    · simp only [primitive, ite_eq_right ht, ite_eq_right ht', mul_zero]

lemma zeroExtension_norm_integral (R : ℝ) (v : ℝ → ℝ) :
    (∫ t : ℝ, ‖zeroExtension R v t‖) = ∫ t in interval R, ‖v t‖ := by
  have he : (fun t => ‖zeroExtension R v t‖) =
      (interval R).indicator (fun t => ‖v t‖) := by
    funext t
    by_cases ht : t ∈ interval R
    · simp [zeroExtension, ht]
    · simp [zeroExtension, ht]
  rw [he]
  exact integral_indicator (s := interval R) (f := fun t => ‖v t‖) measurableSet_Icc

/-- A safe boundedness constant for the actual primitive map. Its purpose is
convergence only; no protected quantitative constant is changed. -/
theorem primitive_square_bound {R : ℝ} (hR : 0 < R) {v : ℝ → ℝ}
    (hv : MemLp v 2 (physicalMeasure R)) :
    (∫ t in interval R, (primitive R v t) ^ 2) ≤
      4 * R ^ 2 * (∫ t in interval R, (v t) ^ 2) := by
  let L : ℝ := ∫ t in interval R, |v t|
  have hL : 0 ≤ L := integral_nonneg (fun t => abs_nonneg _)
  have hp (t : ℝ) : (primitive R v t) ^ 2 ≤ L ^ 2 := by
    have h := primitive_norm_le hv t
    rw [zeroExtension_norm_integral] at h
    simp only [Real.norm_eq_abs] at h
    change |primitive R v t| ≤ L at h
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg (primitive R v t)) hL).2 h
  have hw := RhTail.physical_square_integrable (primitive_memLp hv)
  have hc : Integrable (fun _ : ℝ => L ^ 2) (physicalMeasure R) := integrable_const _
  have hi := integral_mono hw hc hp
  have hvC : (∫ t in interval R, L ^ 2) = (2 * R) * L ^ 2 := by
    simp [interval, integral_const, Real.volume_Icc,
      Real.toNNReal_of_nonneg (by linarith : 0 ≤ R - -R),
      max_eq_left (by linarith : 0 ≤ R + R), two_mul]
  rw [hvC] at hi
  have hL2 : L ^ 2 ≤ 2 * R * (∫ t in interval R, (v t) ^ 2) :=
    RhDilationRank.l1_sq_le hR hv
  have hm := mul_le_mul_of_nonneg_left hL2 (by positivity : 0 ≤ 2 * R)
  nlinarith

end RhPrimitiveApproximation
#print axioms RhPrimitiveApproximation.primitive_add
#print axioms RhPrimitiveApproximation.primitive_smul
#print axioms RhPrimitiveApproximation.primitive_square_bound
