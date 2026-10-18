import RhFlatCoreDilation001
import RhPhysicalShiftFourier001

/-! Exact arbitrary-complex two-delay dilation dictionary on actual L2
representatives. Both delays and all AE substitutions are retained. -/
set_option maxHeartbeats 0
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace RhComplexShiftDilation
open RhWeightedMeasureEmbedding RhFlatSmoothCore RhFlatCoreDilation

def rawPair (f g : ℝ → ℂ) (ell : ℝ) : ℝ :=
  ∫ t, inner ℝ (f t) (g (t + ell)) + inner ℝ (f t) (g (t - ell))

lemma rawPair_congr_ae {f f' g g' : ℝ → ℂ} (hf : f =ᵐ[volume] f')
    (hg : g =ᵐ[volume] g') (ell : ℝ) : rawPair f g ell = rawPair f' g' ell := by
  have hp := (measurePreserving_add_right volume ell).quasiMeasurePreserving.ae hg
  have hn := (measurePreserving_add_right volume (-ell)).quasiMeasurePreserving.ae hg
  unfold rawPair
  apply integral_congr_ae
  filter_upwards [hf, hp, hn] with t ht htp htn
  simp only [sub_eq_add_neg]
  rw [ht, htp, htn]

theorem rawPair_dilate {r : ℝ} (hr : 0 < r) (f g : ℝ → ℂ) (ell : ℝ) :
    rawPair (RhDilation.complexDilate r f) (RhDilation.complexDilate r g) ell =
      rawPair f g (ell / r) := by
  have hs : (Real.sqrt r)⁻¹ * (Real.sqrt r)⁻¹ = r⁻¹ := by
    rw [← mul_inv, ← pow_two, Real.sq_sqrt hr.le]
  have he : (fun t : ℝ =>
      inner ℝ (RhDilation.complexDilate r f t)
        (RhDilation.complexDilate r g (t + ell)) +
      inner ℝ (RhDilation.complexDilate r f t)
        (RhDilation.complexDilate r g (t - ell))) =
      fun t => r⁻¹ * (inner ℝ (f (t / r)) (g (t / r + ell / r)) +
        inner ℝ (f (t / r)) (g (t / r - ell / r))) := by
    funext t
    simp only [RhDilation.complexDilate, add_div, sub_div]
    change inner ℝ ((Real.sqrt r)⁻¹ • f (t / r))
        ((Real.sqrt r)⁻¹ • g (t / r + ell / r)) +
      inner ℝ ((Real.sqrt r)⁻¹ • f (t / r))
        ((Real.sqrt r)⁻¹ • g (t / r - ell / r)) = _
    simp only [real_inner_smul_left, real_inner_smul_right]
    calc
      _ = ((Real.sqrt r)⁻¹ * (Real.sqrt r)⁻¹) *
          (inner ℝ (f (t / r)) (g (t / r + ell / r)) +
           inner ℝ (f (t / r)) (g (t / r - ell / r))) := by ring
      _ = _ := by rw [hs]
  unfold rawPair
  rw [he, integral_const_mul]
  have hi := Measure.integral_comp_div
    (fun t : ℝ => inner ℝ (f t) (g (t + ell / r)) +
      inner ℝ (f t) (g (t - ell / r))) r
  rw [hi, abs_of_pos hr]
  simp only [smul_eq_mul]
  field_simp

/-- The actual flat-core outward map satisfies the native two-delay identity
for arbitrary complex L2 physical images. No real-valued shortcut is used. -/
theorem outward_spatialPair {R r : ℝ} (hr : 1 ≤ r)
    (F G : FlatCoreSpace R) (ell : ℝ) :
    RhPhysicalShiftFourier.spatialPair
      (physicalEmbedding (outwardMap hr F : WeightedSpace))
      (physicalEmbedding (outwardMap hr G : WeightedSpace)) ell =
    RhPhysicalShiftFourier.spatialPair
      (physicalEmbedding (F : WeightedSpace))
      (physicalEmbedding (G : WeightedSpace)) (ell / r) := by
  change rawPair (physicalEmbedding (outwardMap hr F : WeightedSpace))
    (physicalEmbedding (outwardMap hr G : WeightedSpace)) ell =
    rawPair (physicalEmbedding (F : WeightedSpace)) (physicalEmbedding (G : WeightedSpace)) (ell / r)
  rw [rawPair_congr_ae (outwardMap_physical_ae hr F) (outwardMap_physical_ae hr G) ell]
  exact rawPair_dilate (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hr) _ _ _

end RhComplexShiftDilation
#print axioms RhComplexShiftDilation.rawPair_dilate
#print axioms RhComplexShiftDilation.outward_spatialPair
