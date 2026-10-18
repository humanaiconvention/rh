import RhClosedCoreDilation001
import RhWeightedInwardMap001

/-! The actual bounded inward map preserves the concrete closed real smooth
core. Exact inverse identities are compared in the common ambient weighted
space; algebraically equal radii are NOT treated as judgmentally equal.
-/
noncomputable section
open Set MeasureTheory Filter FourierTransform
open scoped Topology ContDiff ENNReal
namespace RhClosedCoreDilationInverse
open RhAnchored RhDilation RhWeightedMeasureEmbedding RhClosedSmoothCore
open RhWeightedDilation RhWeightedDilationMap RhWeightedInwardMap RhClosedCoreDilation

/-- Actual inward image of each strict supported smooth real generator. -/
theorem inward_smooth_generator {R r : ℝ} (hr : 1 ≤ r)
    {F : SupportedSpace R} (hF : F ∈ smoothLiftSet R) :
    inwardMap hr F ∈ smoothLiftSet (r⁻¹ * R) := by
  obtain ⟨f, hfS, _hfC, hfT, hfA⟩ := hF
  have hi : 0 < r⁻¹ := inv_pos.mpr (by linarith : 0 < r)
  refine ⟨dilate r⁻¹ f, dilate_smooth f hfS, dilate_compact hi hfT,
    dilate_strict_support hi hfT, ?_⟩
  have hscaled := ae_comp_div hi hfA
  filter_upwards [inwardMap_physical_ae hr F, hscaled] with t ht hs
  rw [ht]
  simp only [complexDilate, dilate, hs, Complex.ofReal_mul]

/-- Closed preimage in the complete weighted norm supplies inward closure. -/
theorem inward_preserves_core {R r : ℝ} (hr : 1 ≤ r)
    {F : SupportedSpace R} (hF : F ∈ smoothCore R) :
    inwardMap hr F ∈ smoothCore (r⁻¹ * R) := by
  let S : Submodule ℝ (SupportedSpace R) :=
    (smoothCore (r⁻¹ * R)).comap (inwardMap hr).toLinearMap
  have hspan : Submodule.span ℝ (smoothLiftSet R) ≤ S := by
    apply Submodule.span_le.mpr
    intro X hX
    exact smooth_lift_mem_core (inward_smooth_generator hr hX)
  have hclosed : IsClosed (S : Set (SupportedSpace R)) :=
    (smoothCore_isClosed (r⁻¹ * R)).preimage (inwardMap hr).continuous
  have hclosure := (Submodule.span ℝ (smoothLiftSet R)).topologicalClosure_minimal hspan hclosed
  exact hclosure hF

/-- A genuine bounded CLM of actual complete smooth-core Hilbert spaces. -/
def inwardCoreMap {R r : ℝ} (hr : 1 ≤ r) : CoreSpace R →L[ℝ] CoreSpace (r⁻¹ * R) :=
  ((inwardMap hr).comp (smoothCore R).subtypeL).codRestrict (smoothCore (r⁻¹ * R))
    (fun F => inward_preserves_core hr F.property)

theorem inwardCoreMap_norm_le {R r : ℝ} (hr : 1 ≤ r) (F : CoreSpace R) :
    ‖inwardCoreMap hr F‖ ≤ Real.sqrt (1 + 5 * Real.log r) * ‖F‖ :=
  inwardMap_norm_le hr (F : SupportedSpace R)

/-- Native inverse equality with every support and quotient retained. -/
theorem inwardCoreMap_outwardCoreMap_cancel {R r : ℝ} (hr : 1 ≤ r) (F : CoreSpace R) :
    ((inwardCoreMap hr (outwardCoreMap hr F) : SupportedSpace (r⁻¹ * (r * R))) : WeightedSpace) =
      ((F : SupportedSpace R) : WeightedSpace) :=
  inwardMap_outwardMap_cancel hr (F : SupportedSpace R)

theorem outwardCoreMap_inwardCoreMap_cancel {R r : ℝ} (hr : 1 ≤ r) (F : CoreSpace R) :
    ((outwardCoreMap hr (inwardCoreMap hr F) : SupportedSpace (r * (r⁻¹ * R))) : WeightedSpace) =
      ((F : SupportedSpace R) : WeightedSpace) :=
  outwardMap_inwardMap_cancel hr (F : SupportedSpace R)

end RhClosedCoreDilationInverse
#print axioms RhClosedCoreDilationInverse.inward_smooth_generator
#print axioms RhClosedCoreDilationInverse.inward_preserves_core
#print axioms RhClosedCoreDilationInverse.inwardCoreMap_norm_le
#print axioms RhClosedCoreDilationInverse.inwardCoreMap_outwardCoreMap_cancel
#print axioms RhClosedCoreDilationInverse.outwardCoreMap_inwardCoreMap_cancel
