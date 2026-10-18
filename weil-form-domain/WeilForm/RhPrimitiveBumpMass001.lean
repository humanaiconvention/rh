import RhPrimitiveApproximation001

/-! Actual anchored primitives of normalized compact smooth bumps have
vanishing L2 mass as their outer radii shrink. No Sobolev trace is assumed.
-/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology Interval
namespace RhPrimitiveBumpMass
open RhAnchored RhNativeBumpCapacity RhPrimitiveApproximation

lemma normalized_bump_zero_of_outside (φ : ContDiffBump (0 : ℝ))
    {t : ℝ} (ht : φ.rOut ≤ |t|) : φ.normed volume t = 0 := by
  unfold ContDiffBump.normed
  rw [φ.zero_of_le_dist (by simpa only [Real.dist_eq, sub_zero] using ht), zero_div]

/-- The actual assigned-zero representative is also bounded at the anchor. -/
theorem primitive_bump_norm_le_one (φ : ContDiffBump (0 : ℝ)) (R t : ℝ) :
    ‖primitive R (φ.normed volume) t‖ ≤ 1 := by
  have h := primitive_norm_le (normalized_bump_memLp φ R) t
  rw [zeroExtension_norm_integral] at h
  have hn : (fun t => ‖φ.normed volume t‖) = φ.normed volume := by
    funext t
    rw [Real.norm_eq_abs, abs_of_nonneg (φ.nonneg_normed t)]
  rw [hn] at h
  have hm := setIntegral_le_integral (φ.integrable_normed (μ := volume))
    (Eventually.of_forall (φ.nonneg_normed (μ := volume))) (s := interval R)
  rw [φ.integral_normed] at hm
  exact h.trans hm

/-- No primitive mass survives outside the source bump's own support interval. -/
theorem primitive_bump_zero_of_outside (φ : ContDiffBump (0 : ℝ))
    {R t : ℝ} (hR : φ.rOut ≤ R) (ht : φ.rOut ≤ |t|) :
    primitive R (φ.normed volume) t = 0 := by
  by_cases ht0 : t < 0
  · have htL : t ≤ -φ.rOut := by
      rw [abs_of_neg ht0] at ht
      linarith
    rw [primitive_eq_left (φ.normed volume) ht0]
    unfold leftPrimitive
    have he : EqOn (zeroExtension R (φ.normed volume)) (fun _ => (0 : ℝ))
        (uIcc (-R) t) := by
      intro u hu
      change min (-R) t ≤ u ∧ u ≤ max (-R) t at hu
      have huL : u ≤ -φ.rOut := hu.2.trans (max_le (by linarith) htL)
      have huabs : φ.rOut ≤ |u| := by linarith [neg_le_abs u]
      have hz := normalized_bump_zero_of_outside φ huabs
      by_cases huR : u ∈ interval R
      · simp only [zeroExtension_eq huR, hz]
      · simp only [zeroExtension_eq_zero huR]
    simpa only [intervalIntegral.integral_zero] using intervalIntegral.integral_congr he
  · have htN : 0 ≤ t := le_of_not_gt ht0
    rw [abs_of_nonneg htN] at ht
    have htP : 0 < t := lt_of_lt_of_le φ.rOut_pos ht
    rw [primitive_eq_right (φ.normed volume) htP]
    unfold rightPrimitive
    have he : EqOn (zeroExtension R (φ.normed volume)) (fun _ => (0 : ℝ))
        (uIcc R t) := by
      intro u hu
      change min R t ≤ u ∧ u ≤ max R t at hu
      have huL : φ.rOut ≤ u := (le_min hR ht).trans hu.1
      have huabs : φ.rOut ≤ |u| := huL.trans (le_abs_self u)
      have hz := normalized_bump_zero_of_outside φ huabs
      by_cases huR : u ∈ interval R
      · simp only [zeroExtension_eq huR, hz]
      · simp only [zeroExtension_eq_zero huR]
    simpa only [intervalIntegral.integral_zero] using intervalIntegral.integral_congr he

/-- Exact shrinking-support L2 mass bound, independent of the fixed outer radius. -/
theorem primitive_bump_square_bound (φ : ContDiffBump (0 : ℝ))
    {R : ℝ} (hR : φ.rOut ≤ R) :
    (∫ t in interval R, (primitive R (φ.normed volume) t) ^ 2) ≤ 2 * φ.rOut := by
  let δ : ℝ := φ.rOut
  have hδ : 0 < δ := φ.rOut_pos
  have hp (t : ℝ) : (primitive R (φ.normed volume) t) ^ 2 ≤
      (interval δ).indicator (fun _ => (1 : ℝ)) t := by
    by_cases ht : t ∈ interval δ
    · rw [indicator_of_mem ht]
      have hh := primitive_bump_norm_le_one φ R t
      have hs : |primitive R (φ.normed volume) t| ≤ 1 := by
        simpa only [Real.norm_eq_abs] using hh
      simpa only [sq_abs, one_pow] using (sq_le_sq₀
        (abs_nonneg (primitive R (φ.normed volume) t)) (by norm_num : (0 : ℝ) ≤ 1)).2 hs
    · rw [indicator_of_notMem ht]
      have habs : φ.rOut ≤ |t| := by
        by_contra hn
        have hs : |t| ≤ δ := le_of_lt (lt_of_not_ge hn)
        apply ht
        exact abs_le.mp hs
      rw [primitive_bump_zero_of_outside φ hR habs]
      norm_num
  have hw := RhTail.physical_square_integrable (primitive_memLp (normalized_bump_memLp φ R))
  have hi : Integrable ((interval δ).indicator (fun _ => (1 : ℝ))) (physicalMeasure R) :=
    (integrable_const _).indicator measurableSet_Icc
  have h := integral_mono hw hi hp
  have hsub : interval δ ⊆ interval R := by
    intro t ht
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hm : (physicalMeasure R).restrict (interval δ) = physicalMeasure δ :=
    Measure.restrict_restrict_of_subset hsub
  have he : (∫ t in interval R, (interval δ).indicator (fun _ => (1 : ℝ)) t) = 2 * δ := by
    change (∫ t, (interval δ).indicator (fun _ => (1 : ℝ)) t ∂physicalMeasure R) = 2 * δ
    rw [integral_indicator (μ := physicalMeasure R) (s := interval δ)
      (f := fun _ : ℝ => (1 : ℝ)) measurableSet_Icc, hm]
    simp [physicalMeasure, interval, integral_const,
      max_eq_left (by linarith : 0 ≤ δ + δ), two_mul]
  rw [he] at h
  exact h

/-- The concentrating family has vanishing actual primitive L2 mass. -/
theorem primitive_bump_square_tendsto_zero
    (φ : ℕ → ContDiffBump (0 : ℝ))
    (hφ : Tendsto (fun n => (φ n).rOut) atTop (𝓝 0))
    {R : ℝ} (hR : 0 < R) :
    Tendsto (fun n => ∫ t in interval R,
      (primitive R ((φ n).normed volume) t) ^ 2) atTop (𝓝 0) := by
  have he : ∀ᶠ n in atTop, (φ n).rOut < R := (tendsto_order.mp hφ).2 R hR
  apply squeeze_zero' (Eventually.of_forall (fun n => integral_nonneg (fun _ => sq_nonneg _)))
  · filter_upwards [he] with n hn
    exact primitive_bump_square_bound (φ n) hn.le
  · simpa only [mul_zero] using hφ.const_mul 2

end RhPrimitiveBumpMass
#print axioms RhPrimitiveBumpMass.primitive_bump_norm_le_one
#print axioms RhPrimitiveBumpMass.primitive_bump_zero_of_outside
#print axioms RhPrimitiveBumpMass.primitive_bump_square_bound
#print axioms RhPrimitiveBumpMass.primitive_bump_square_tendsto_zero
