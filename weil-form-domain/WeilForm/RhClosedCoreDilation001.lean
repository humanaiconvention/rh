import RhClosedSmoothCore001
import RhWeightedDilationMap001

/-! Preservation of the concrete real closed smooth core under the ACTUAL
outward complete-norm dilation map. Generators are scaled with their exact
physical AE representative; continuity then transfers the complete closed
span. No global positivity or spectral assertion is made.
-/
noncomputable section
open Set MeasureTheory Filter FourierTransform
open scoped Topology ContDiff ENNReal
namespace RhClosedCoreDilation
open RhAnchored RhDilation RhWeightedMeasureEmbedding RhClosedSmoothCore
open RhWeightedDilation RhWeightedDilationMap

lemma dilate_smooth {r : ℝ} (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (dilate r f) := by
  unfold dilate
  exact contDiff_const.mul (hf.comp (contDiff_id.div_const r))

/-- The closure of the support scales inside the SAME open enlarged window. -/
lemma dilate_strict_support {R r : ℝ} (hr : 0 < r) {f : ℝ → ℝ}
    (hf : tsupport f ⊆ Ioo (-R) R) :
    tsupport (dilate r f) ⊆ Ioo (-(r * R)) (r * R) := by
  have hs : Function.support (dilate r f) ⊆ (fun t : ℝ => t / r) ⁻¹' tsupport f := by
    intro t ht
    apply subset_tsupport f
    intro hz
    exact ht (by simp [dilate, hz])
  have hcl : tsupport (dilate r f) ⊆ (fun t : ℝ => t / r) ⁻¹' tsupport f :=
    closure_minimal hs (isClosed_closure.preimage (continuous_id.div_const r))
  intro t ht
  have hmem := hf (hcl ht)
  have hlo := (lt_div_iff₀ hr).mp hmem.1
  have hhi := (div_lt_iff₀ hr).mp hmem.2
  constructor <;> nlinarith

lemma dilate_compact {R r : ℝ} (hr : 0 < r) {f : ℝ → ℝ}
    (hf : tsupport f ⊆ Ioo (-R) R) : HasCompactSupport (dilate r f) := by
  apply isCompact_Icc.of_isClosed_subset isClosed_closure
  intro t ht
  have hi := dilate_strict_support hr hf ht
  exact ⟨hi.1.le, hi.2.le⟩

/-- Actual generator mapping; all nonsingular AE substitutions are explicit. -/
theorem outward_smooth_generator {R r : ℝ} (hr : 1 ≤ r)
    {F : SupportedSpace R} (hF : F ∈ smoothLiftSet R) :
    outwardMap hr F ∈ smoothLiftSet (r * R) := by
  obtain ⟨f, hfS, _hfC, hfT, hfA⟩ := hF
  have hr0 : 0 < r := by linarith
  refine ⟨dilate r f, dilate_smooth f hfS, dilate_compact hr0 hfT,
    dilate_strict_support hr0 hfT, ?_⟩
  have hscaled := ae_comp_div hr0 hfA
  filter_upwards [outwardMap_physical_ae hr F, hscaled] with t ht hs
  rw [ht]
  simp [complexDilate, dilate, hs]

/-- Actual complete-form closed-core preservation. The inverse image is closed
in the complete weighted norm, not merely in physical L2 mass. -/
theorem outward_preserves_core {R r : ℝ} (hr : 1 ≤ r)
    {F : SupportedSpace R} (hF : F ∈ smoothCore R) :
    outwardMap hr F ∈ smoothCore (r * R) := by
  let S : Submodule ℝ (SupportedSpace R) :=
    (smoothCore (r * R)).comap (outwardMap hr).toLinearMap
  have hspan : Submodule.span ℝ (smoothLiftSet R) ≤ S := by
    apply Submodule.span_le.mpr
    intro X hX
    exact smooth_lift_mem_core (outward_smooth_generator hr hX)
  have hclosed : IsClosed (S : Set (SupportedSpace R)) :=
    (smoothCore_isClosed (r * R)).preimage (outwardMap hr).continuous
  have hclosure := (Submodule.span ℝ (smoothLiftSet R)).topologicalClosure_minimal hspan hclosed
  exact hclosure hF

/-- Dilation on the actual complete smooth-core Hilbert spaces, obtained by
codomain restriction from the already constructed physical dilation map. -/
def outwardCoreMap {R r : ℝ} (hr : 1 ≤ r) : CoreSpace R →L[ℝ] CoreSpace (r * R) :=
  ((outwardMap hr).comp (smoothCore R).subtypeL).codRestrict (smoothCore (r * R))
    (fun F => outward_preserves_core hr F.property)

theorem outwardCoreMap_norm_le {R r : ℝ} (hr : 1 ≤ r) (F : CoreSpace R) :
    ‖outwardCoreMap hr F‖ ≤ ‖F‖ :=
  outwardMap_norm_le hr (F : SupportedSpace R)

end RhClosedCoreDilation
#print axioms RhClosedCoreDilation.dilate_strict_support
#print axioms RhClosedCoreDilation.outward_smooth_generator
#print axioms RhClosedCoreDilation.outward_preserves_core
#print axioms RhClosedCoreDilation.outwardCoreMap_norm_le
