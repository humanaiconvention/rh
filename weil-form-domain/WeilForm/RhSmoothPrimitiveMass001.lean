import RhSmoothPrimitiveCore001

noncomputable section
open Set MeasureTheory
open scoped Topology ContDiff
namespace RhSmoothPrimitiveMass
open RhAnchored RhSmoothPrimitiveCore

lemma totalMass_eq_integral {R : ℝ} {z : ℝ → ℝ}
    (hs : Function.support z ⊆ interval R) : totalMass R z = ∫ u : ℝ, z u := by
  change Function.support z ⊆ Icc (-R) R at hs
  unfold totalMass
  change (∫ u in Icc (-R) R, z u) = ∫ u : ℝ, z u
  rw [← integral_indicator measurableSet_Icc, indicator_eq_self.mpr hs]

/-- The smooth primitive core helper accepts the native physical zero-mass
condition, not only a whole-line normalization. -/
theorem exists_smooth_compact_primitive {R : ℝ} (hR : 0 < R) {z : ℝ → ℝ}
    (hz : ContDiff ℝ ∞ z) (hc : HasCompactSupport z)
    (hs : tsupport z ⊆ Ioo (-R) R) (hzero : totalMass R z = 0) :
    ∃ f : ℝ → ℝ, ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧
      tsupport f ⊆ Ioo (-R) R ∧ deriv f = z ∧
      f =ᵐ[volume] zeroExtension R (primitive R z) := by
  have hsI : Function.support z ⊆ interval R := by
    intro t ht
    have h := hs (subset_tsupport z ht)
    exact ⟨h.1.le, h.2.le⟩
  apply RhSmoothPrimitiveCore.exists_smooth_compact_primitive hR hz hc hs
  rw [← totalMass_eq_integral hsI]
  exact hzero

end RhSmoothPrimitiveMass
#print axioms RhSmoothPrimitiveMass.totalMass_eq_integral
#print axioms RhSmoothPrimitiveMass.exists_smooth_compact_primitive
