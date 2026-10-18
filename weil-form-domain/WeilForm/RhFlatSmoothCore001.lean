import RhClosedSmoothCore001

/-!
The SAME real smooth physical generators, flattened directly into the actual
weighted Hilbert space. The norm and kernel are unchanged. Equality with the
ambient image of the original nested closed core is proved, not presumed.
-/
noncomputable section
open Set MeasureTheory Filter FourierTransform
open scoped Topology ContDiff ENNReal
namespace RhFlatSmoothCore
open RhAnchored RhWeightedMeasureEmbedding RhWeightedPrimitiveLift RhActualWeightedClosure

/-- Same actual real compact smooth representatives and strict support window. -/
def smoothWeightedSet (R : ℝ) : Set WeightedSpace :=
  {F | ∃ f : ℝ → ℝ, ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧
    tsupport f ⊆ Ioo (-R) R ∧ physicalEmbedding F =ᵐ[volume] fun t => (f t : ℂ)}

/-- Single-submodule realization, with the original complete weighted norm. -/
def flatCore (R : ℝ) : Submodule ℝ WeightedSpace :=
  (Submodule.span ℝ (smoothWeightedSet R)).topologicalClosure

abbrev FlatCoreSpace (R : ℝ) := ↥(flatCore R)

lemma flatCore_isClosed (R : ℝ) : IsClosed (flatCore R : Set WeightedSpace) :=
  (Submodule.span ℝ (smoothWeightedSet R)).isClosed_topologicalClosure

instance flatCore_complete (R : ℝ) : CompleteSpace (FlatCoreSpace R) :=
  (flatCore_isClosed R).completeSpace_coe

lemma smooth_generator_supported {R : ℝ} {F : WeightedSpace}
    (hF : F ∈ smoothWeightedSet R) : F ∈ supportedSubspace R := by
  obtain ⟨f, _hfS, _hfC, hfT, hfA⟩ := hF
  rw [mem_supportedSubspace_iff]
  filter_upwards [hfA] with t ht
  intro hout
  rw [ht]
  have hz : f t = 0 := by
    by_contra hn
    have hi := hfT (subset_tsupport f hn)
    exact hout ⟨hi.1.le, hi.2.le⟩
  simp [hz]

lemma smooth_generator_mem {R : ℝ} {F : WeightedSpace} (hF : F ∈ smoothWeightedSet R) :
    F ∈ flatCore R :=
  (Submodule.le_topologicalClosure _) (Submodule.subset_span hF)

/-- Every vector in the actual closed smooth core remains physically supported. -/
theorem flatCore_supported (R : ℝ) : flatCore R ≤ supportedSubspace R :=
  (Submodule.span ℝ (smoothWeightedSet R)).topologicalClosure_minimal
    (Submodule.span_le.mpr (fun _ h => smooth_generator_supported h))
    (supportedSubspace_isClosed R)

/-- Literal equality of the old and flattened generator predicates. -/
lemma supported_smooth_iff {R : ℝ} (X : SupportedSpace R) :
    X ∈ RhClosedSmoothCore.smoothLiftSet R ↔ (X : WeightedSpace) ∈ smoothWeightedSet R :=
  Iff.rfl

/-- The previous nested closure maps into this concrete single-submodule closure. -/
lemma nested_core_mem_flat {R : ℝ} {X : SupportedSpace R}
    (hX : X ∈ RhClosedSmoothCore.smoothCore R) : (X : WeightedSpace) ∈ flatCore R := by
  let S : Submodule ℝ (SupportedSpace R) :=
    (flatCore R).comap (supportedSubspace R).subtype
  have hspan : Submodule.span ℝ (RhClosedSmoothCore.smoothLiftSet R) ≤ S := by
    apply Submodule.span_le.mpr
    intro Y hY
    exact smooth_generator_mem ((supported_smooth_iff Y).mp hY)
  have hclosed : IsClosed (S : Set (SupportedSpace R)) :=
    (flatCore_isClosed R).preimage (supportedSubspace R).subtypeL.continuous
  exact ((Submodule.span ℝ (RhClosedSmoothCore.smoothLiftSet R)).topologicalClosure_minimal
    hspan hclosed) hX

/-- Actual weighted-space image of the previously constructed nested core. -/
def nestedImage (R : ℝ) : Submodule ℝ WeightedSpace :=
  (RhClosedSmoothCore.smoothCore R).map (supportedSubspace R).subtype

lemma nestedImage_isClosed (R : ℝ) : IsClosed (nestedImage R : Set WeightedSpace) := by
  have h := ((supportedSubspace R).isClosedEmbedding_subtype (supportedSubspace_isClosed R)).isClosedMap
    (RhClosedSmoothCore.smoothCore R : Set (SupportedSpace R))
    (RhClosedSmoothCore.smoothCore_isClosed R)
  exact h

/-- This is a representation change of the SAME closed real smooth core. -/
theorem flatCore_eq_nestedImage (R : ℝ) : flatCore R = nestedImage R := by
  apply le_antisymm
  · apply (Submodule.span ℝ (smoothWeightedSet R)).topologicalClosure_minimal
    · apply Submodule.span_le.mpr
      intro F hF
      let X : SupportedSpace R := ⟨F, smooth_generator_supported hF⟩
      exact ⟨X, RhClosedSmoothCore.smooth_lift_mem_core ((supported_smooth_iff X).mpr hF), rfl⟩
    · exact nestedImage_isClosed R
  · rintro F ⟨X, hX, rfl⟩
    exact nested_core_mem_flat hX

/-- Actual primitive inclusion reuses the certified literal weighted approximation. -/
theorem actualPrimitiveLift_mem_flatCore {R : ℝ} (hR : 0 < R) (v : ℝ → ℝ)
    (hv : MemLp v 2 (physicalMeasure R)) : actualPrimitiveLift hR v hv ∈ flatCore R := by
  obtain ⟨f, X, hfS, hfC, hfT, hfA, hNorm⟩ := actual_smooth_weighted_approximation hR hv
  let Y : ℕ → WeightedSpace := fun n => (X n : WeightedSpace)
  have hY (n : ℕ) : Y n ∈ flatCore R :=
    smooth_generator_mem ⟨f n, hfS n, hfC n, hfT n, hfA n⟩
  have hn : Tendsto (fun n => ‖Y n - actualPrimitiveLift hR v hv‖) atTop (𝓝 0) := hNorm
  exact (flatCore_isClosed R).mem_of_tendsto
    (tendsto_iff_norm_sub_tendsto_zero.mpr hn) (Eventually.of_forall hY)

def actualFlatCoreLift {R : ℝ} (hR : 0 < R) (v : ℝ → ℝ)
    (hv : MemLp v 2 (physicalMeasure R)) : FlatCoreSpace R :=
  ⟨actualPrimitiveLift hR v hv, actualPrimitiveLift_mem_flatCore hR v hv⟩

end RhFlatSmoothCore
#print axioms RhFlatSmoothCore.flatCore_isClosed
#print axioms RhFlatSmoothCore.flatCore_supported
#print axioms RhFlatSmoothCore.flatCore_eq_nestedImage
#print axioms RhFlatSmoothCore.actualPrimitiveLift_mem_flatCore
