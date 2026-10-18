import RhAnchoredSpace001
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Topology.Order.Compact

/-! Smooth zero-mass physical derivatives have a genuinely smooth compact
ordinary primitive. Its relation to the saved anchored representative is AE,
including the potentially different assigned value at zero. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology Interval ContDiff
namespace RhSmoothPrimitiveCore
open RhAnchored

def smoothPrimitive (R : ℝ) (z : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ u in (-R)..t, z u

lemma smoothPrimitive_hasDerivAt (R : ℝ) {z : ℝ → ℝ}
    (hz : Continuous z) (t : ℝ) :
    HasDerivAt (smoothPrimitive R z) (z t) t := by
  exact intervalIntegral.integral_hasDerivAt_right (hz.intervalIntegrable _ _)
    hz.aestronglyMeasurable.stronglyMeasurableAtFilter hz.continuousAt

lemma smoothPrimitive_contDiff (R : ℝ) {z : ℝ → ℝ}
    (hz : ContDiff ℝ ∞ z) : ContDiff ℝ ∞ (smoothPrimitive R z) := by
  apply contDiff_infty_iff_deriv.mpr
  refine ⟨fun t => (smoothPrimitive_hasDerivAt R hz.continuous t).differentiableAt, ?_⟩
  have hd : deriv (smoothPrimitive R z) = z := by
    funext t
    exact (smoothPrimitive_hasDerivAt R hz.continuous t).deriv
  rw [hd]
  exact hz

lemma smoothPrimitive_zero_left {R B t : ℝ} (hBR : B < R)
    {z : ℝ → ℝ} (hB : Function.support z ⊆ Icc (-B) B) (ht : t ≤ -B) :
    smoothPrimitive R z t = 0 := by
  unfold smoothPrimitive
  calc
    _ = ∫ u in (-R)..t, (0 : ℝ) := by
      apply intervalIntegral.integral_congr_uIoo
      intro u hu
      have humax : u < max (-R) t := hu.2
      have huB : u < -B := humax.trans_le (max_le (by linarith) ht)
      by_contra hzu
      have huI := hB hzu
      linarith [huI.1]
    _ = 0 := by simp

lemma smoothPrimitive_zero_right {R B t : ℝ} (hBR : B < R)
    {z : ℝ → ℝ} (hB : Function.support z ⊆ Icc (-B) B)
    (hzero : (∫ u : ℝ, z u) = 0) (ht : B ≤ t) :
    smoothPrimitive R z t = 0 := by
  have hs : Function.support z ⊆ Ioc (-R) t := by
    intro u hu
    have huI := hB hu
    constructor <;> linarith [huI.1, huI.2]
  unfold smoothPrimitive
  rw [intervalIntegral.integral_eq_integral_of_support_subset hs, hzero]

lemma smoothPrimitive_tsupport_subset {R B : ℝ} (hBR : B < R)
    {z : ℝ → ℝ} (hB : Function.support z ⊆ Icc (-B) B)
    (hzero : (∫ u : ℝ, z u) = 0) :
    tsupport (smoothPrimitive R z) ⊆ Icc (-B) B := by
  apply closure_minimal _ isClosed_Icc
  intro t ht
  by_contra htn
  change smoothPrimitive R z t ≠ 0 at ht
  simp only [mem_Icc, not_and_or, not_le] at htn
  rcases htn with htl | htr
  · exact ht (smoothPrimitive_zero_left hBR hB htl.le)
  · exact ht (smoothPrimitive_zero_right hBR hB hzero htr.le)

lemma smaller_support_interval {R : ℝ} (hR : 0 < R) {z : ℝ → ℝ}
    (hc : HasCompactSupport z) (hs : tsupport z ⊆ Ioo (-R) R) :
    ∃ B : ℝ, 0 < B ∧ B < R ∧ tsupport z ⊆ Icc (-B) B := by
  by_cases hn : (tsupport z).Nonempty
  · obtain ⟨x, hx, hmax⟩ := hc.isCompact.exists_isMaxOn hn continuous_abs.continuousOn
    have hxR : |x| < R := abs_lt.mpr (hs hx)
    refine ⟨(|x| + R) / 2, by positivity, by linarith, ?_⟩
    intro t ht
    have htx : |t| ≤ |x| := hmax ht
    exact abs_le.mp (by linarith : |t| ≤ (|x| + R) / 2)
  · refine ⟨R / 2, by positivity, by linarith, ?_⟩
    intro t ht
    exact (hn ⟨t, ht⟩).elim

lemma zeroExtension_eq_self {R : ℝ} {z : ℝ → ℝ}
    (hs : Function.support z ⊆ interval R) : zeroExtension R z = z := by
  exact indicator_eq_self.mpr hs

lemma smoothPrimitive_eq_anchored_of_ne_zero {R B t : ℝ} (hBR : B < R)
    {z : ℝ → ℝ} (hz : Integrable z)
    (hB : Function.support z ⊆ Icc (-B) B)
    (hzero : (∫ u : ℝ, z u) = 0) (ht : t ≠ 0) :
    smoothPrimitive R z t = primitive R z t := by
  have hsI : Function.support z ⊆ interval R := by
    intro u hu
    have huI := hB hu
    constructor <;> linarith [huI.1, huI.2]
  have hze := zeroExtension_eq_self hsI
  have hm : (∫ u in (-R)..R, z u) = 0 := by
    rw [intervalIntegral.integral_eq_integral_of_support_subset]
    · exact hzero
    · intro u hu
      have huI := hB hu
      constructor <;> linarith [huI.1, huI.2]
  by_cases htn : t < 0
  · rw [primitive_eq_left z htn]
    unfold smoothPrimitive leftPrimitive
    rw [hze]
  · have htp : 0 < t := lt_of_le_of_ne (le_of_not_gt htn) (Ne.symm ht)
    rw [primitive_eq_right z htp]
    unfold smoothPrimitive rightPrimitive
    rw [hze]
    have hadj := intervalIntegral.integral_add_adjacent_intervals
      (hz.intervalIntegrable (a := -R) (b := R))
      (hz.intervalIntegrable (a := R) (b := t))
    rw [hm, zero_add] at hadj
    exact hadj.symm

lemma smoothPrimitive_ae_anchored {R B : ℝ} (hBR : B < R)
    {z : ℝ → ℝ} (hz : Integrable z)
    (hB : Function.support z ⊆ Icc (-B) B)
    (hzero : (∫ u : ℝ, z u) = 0) :
    smoothPrimitive R z =ᵐ[volume] zeroExtension R (primitive R z) := by
  have h0 : ∀ᵐ t ∂volume, t ≠ (0 : ℝ) := by
    have h : volume ({0} : Set ℝ) = 0 := by simp
    rw [measure_eq_zero_iff_ae_notMem] at h
    simpa only [mem_singleton_iff] using h
  filter_upwards [h0] with t ht
  by_cases htI : t ∈ interval R
  · rw [zeroExtension_eq htI]
    exact smoothPrimitive_eq_anchored_of_ne_zero hBR hz hB hzero ht
  · rw [zeroExtension_eq_zero htI]
    have hfB := smoothPrimitive_tsupport_subset hBR hB hzero
    by_contra hf
    have htB := hfB (subset_tsupport _ hf)
    apply htI
    constructor <;> linarith [htB.1, htB.2]

/-- Geometric core helper: genuine C-infinity compact primitive, strict support,
exact derivative, and only AE equality to the saved anchored convention. -/
theorem exists_smooth_compact_primitive {R : ℝ} (hR : 0 < R) {z : ℝ → ℝ}
    (hz : ContDiff ℝ ∞ z) (hc : HasCompactSupport z)
    (hs : tsupport z ⊆ Ioo (-R) R) (hzero : (∫ u : ℝ, z u) = 0) :
    ∃ f : ℝ → ℝ, ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧
      tsupport f ⊆ Ioo (-R) R ∧ deriv f = z ∧
      f =ᵐ[volume] zeroExtension R (primitive R z) := by
  obtain ⟨B, hB0, hBR, hzB⟩ := smaller_support_interval hR hc hs
  have hzS : Function.support z ⊆ Icc (-B) B := (subset_tsupport z).trans hzB
  have hfB := smoothPrimitive_tsupport_subset hBR hzS hzero
  refine ⟨smoothPrimitive R z, smoothPrimitive_contDiff R hz, ?_, ?_, ?_, ?_⟩
  · exact isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) hfB
  · intro t ht
    have htB := hfB ht
    constructor <;> linarith [htB.1, htB.2]
  · funext t
    exact (smoothPrimitive_hasDerivAt R hz.continuous t).deriv
  · exact smoothPrimitive_ae_anchored hBR (hz.continuous.integrable_of_hasCompactSupport hc)
      hzS hzero

end RhSmoothPrimitiveCore
#print axioms RhSmoothPrimitiveCore.smoothPrimitive_contDiff
#print axioms RhSmoothPrimitiveCore.smoothPrimitive_ae_anchored
#print axioms RhSmoothPrimitiveCore.exists_smooth_compact_primitive
