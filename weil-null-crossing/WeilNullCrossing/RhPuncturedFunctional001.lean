import RhPuncturedSmoothCore001
import RhNativeCompleteBilinear001

/-! PRIVATE restricted-functional consequence of unconditional punctured-core
density. No ambient extension or finite-point distribution theorem is used.
The native row conclusion is conditional on its actual punctured test values;
this module does not prove arithmetic flux cancellation. -/
set_option maxHeartbeats 150000
noncomputable section
open Set MeasureTheory Filter
open scoped Topology ContDiff
namespace RhPuncturedFunctional
open RhWeightedMeasureEmbedding RhFlatSmoothCore RhPuncturedSmoothCore
open RhNativeCompleteBilinear

/-- A functional on the actual restricted complete domain is determined by
smooth tests avoiding any finite point set. -/
theorem functional_zero_of_punctured (R : ℝ) (F : Finset ℝ)
    (T : FlatCoreSpace R →L[ℝ] ℝ)
    (hT : ∀ X : FlatCoreSpace R,
      (X : WeightedSpace) ∈ puncturedWeightedSet R F → T X = 0) : T = 0 := by
  let S : Submodule ℝ WeightedSpace := T.ker.map (flatCore R).subtype
  have hclosed : IsClosed (S : Set WeightedSpace) := by
    exact ((flatCore R).isClosedEmbedding_subtype (flatCore_isClosed R)).isClosedMap
      (T.ker : Set (FlatCoreSpace R)) T.isClosed_ker
  have hspan : Submodule.span ℝ (puncturedWeightedSet R F) ≤ S := by
    apply Submodule.span_le.mpr
    intro X hX
    have hx : X ∈ flatCore R :=
      puncturedCore_le_flat R F (Submodule.le_topologicalClosure _ (Submodule.subset_span hX))
    let x : FlatCoreSpace R := ⟨X,hx⟩
    exact ⟨x,hT x hX,rfl⟩
  have hall : flatCore R ≤ S := by
    rw [←puncturedCore_eq_flat R F]
    exact (Submodule.span ℝ (puncturedWeightedSet R F)).topologicalClosure_minimal hspan hclosed
  apply ContinuousLinearMap.ext
  intro x
  change T x = 0
  obtain ⟨y,hy,he⟩ := hall x.property
  have hyx : y = x := Subtype.ext he
  rw [←hyx]
  exact hy

/-- The actual complete native row, with literal scalar and fixed horizon. -/
def nativeRow (R C : ℝ) (N : ℕ) (p : WeightedSpace) : FlatCoreSpace R →L[ℝ] ℝ :=
  (completeForm R C N p).comp (flatCore R).subtypeL

/-- If the WHOLE native row vanishes on punctured smooth tests, it vanishes
on the full complete domain. No componentwise arithmetic substitution occurs. -/
theorem native_row_zero_of_punctured (R C : ℝ) (N : ℕ) (F : Finset ℝ)
    (p : WeightedSpace)
    (hrow : ∀ X : FlatCoreSpace R,
      (X : WeightedSpace) ∈ puncturedWeightedSet R F →
        completeForm R C N p (X : WeightedSpace) = 0) :
    ∀ X : FlatCoreSpace R, completeForm R C N p (X : WeightedSpace) = 0 := by
  have hz : nativeRow R C N p = 0 := functional_zero_of_punctured R F
    (nativeRow R C N p) hrow
  intro X
  change nativeRow R C N p X = 0
  rw [hz]
  rfl

end RhPuncturedFunctional
#print axioms RhPuncturedFunctional.functional_zero_of_punctured
#print axioms RhPuncturedFunctional.native_row_zero_of_punctured