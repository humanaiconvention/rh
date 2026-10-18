import RhActualWeightedClosure001
import Mathlib.Topology.Algebra.Module.Basic

/-!
The concrete closed real smooth-core subspace of the supported weighted
Hilbert domain. Actual physical primitives belong by the constructed norm
approximation theorem. Equality with the entire supported domain, and any
positivity statement, are deliberately not asserted.
-/
noncomputable section
open Set MeasureTheory Filter FourierTransform
open scoped Topology ContDiff ENNReal
namespace RhClosedSmoothCore
open RhAnchored RhWeightedMeasureEmbedding RhWeightedPrimitiveLift RhActualWeightedClosure

/-- Actual supported weighted vectors whose physical image is a genuine real
smooth compact function strictly inside the declared support window. -/
def smoothLiftSet (R : ℝ) : Set (SupportedSpace R) :=
  {X | ∃ f : ℝ → ℝ, ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧
    tsupport f ⊆ Ioo (-R) R ∧
    physicalEmbedding (X : WeightedSpace) =ᵐ[volume] fun t => (f t : ℂ)}

/-- A concrete closed subspace, not a postulated complete-form target. -/
def smoothCore (R : ℝ) : Submodule ℝ (SupportedSpace R) :=
  (Submodule.span ℝ (smoothLiftSet R)).topologicalClosure

abbrev CoreSpace (R : ℝ) := ↥(smoothCore R)

lemma smoothCore_isClosed (R : ℝ) : IsClosed (smoothCore R : Set (SupportedSpace R)) :=
  (Submodule.span ℝ (smoothLiftSet R)).isClosed_topologicalClosure

instance coreSpace_complete (R : ℝ) : CompleteSpace (CoreSpace R) :=
  (smoothCore_isClosed R).completeSpace_coe

@[instance_reducible]
def coreRealHilbert (R : ℝ) : InnerProductSpace ℝ (CoreSpace R) := inferInstance

lemma smooth_lift_mem_core {R : ℝ} {X : SupportedSpace R} (hX : X ∈ smoothLiftSet R) :
    X ∈ smoothCore R :=
  (Submodule.le_topologicalClosure _) (Submodule.subset_span hX)

/-- The actual primitive class is contained in the closed smooth core. This is
one-way domain inclusion, not a generic full-domain density assertion. -/
theorem actualPrimitiveSupportedLift_mem_core {R : ℝ} (hR : 0 < R)
    (v : ℝ → ℝ) (hv : MemLp v 2 (physicalMeasure R)) :
    actualPrimitiveSupportedLift hR v hv ∈ smoothCore R := by
  obtain ⟨f, X, hfS, hfC, hfT, hImage, hNorm⟩ :=
    actual_smooth_weighted_approximation hR hv
  have hX (n : ℕ) : X n ∈ smoothCore R :=
    smooth_lift_mem_core ⟨f n, hfS n, hfC n, hfT n, hImage n⟩
  have hTendsto : Tendsto X atTop (𝓝 (actualPrimitiveSupportedLift hR v hv)) :=
    tendsto_iff_norm_sub_tendsto_zero.mpr hNorm
  exact (smoothCore_isClosed R).mem_of_tendsto hTendsto (Eventually.of_forall hX)

/-- An actual physical primitive as an element of the complete real smooth-core
Hilbert space, constructed from the proved inclusion. -/
def actualCoreLift {R : ℝ} (hR : 0 < R) (v : ℝ → ℝ)
    (hv : MemLp v 2 (physicalMeasure R)) : CoreSpace R :=
  ⟨actualPrimitiveSupportedLift hR v hv, actualPrimitiveSupportedLift_mem_core hR v hv⟩

/-- Its physical representative remains the original actual primitive class. -/
theorem actualCoreLift_physical {R : ℝ} (hR : 0 < R) (v : ℝ → ℝ)
    (hv : MemLp v 2 (physicalMeasure R)) :
    physicalEmbedding ((actualCoreLift hR v hv : SupportedSpace R) : WeightedSpace) =
      RhTail.physicalFourierVector R (primitive R v) (primitive_memLp hv) :=
  actualPrimitiveLift_physical hR v hv

/-- The core inherits precisely the complete graph norm already certified for
actual primitives; changing subspaces does not alter any radius or weight. -/
theorem actualCoreLift_norm_square {R : ℝ} (hR : 0 < R) (v : ℝ → ℝ)
    (hv : MemLp v 2 (physicalMeasure R)) :
    ‖actualCoreLift hR v hv‖ ^ 2 =
      (∫ t in interval R, (primitive R v t) ^ 2) +
      (RhTail.fullFrequencyEnergy (1 / 2)
        (RhTail.physicalFourierVector R (primitive R v) (primitive_memLp hv))).toReal :=
  actualPrimitiveSupportedLift_norm_square hR v hv

end RhClosedSmoothCore
#print axioms RhClosedSmoothCore.smoothCore_isClosed
#print axioms RhClosedSmoothCore.coreSpace_complete
#print axioms RhClosedSmoothCore.actualPrimitiveSupportedLift_mem_core
#print axioms RhClosedSmoothCore.actualCoreLift_physical
#print axioms RhClosedSmoothCore.actualCoreLift_norm_square
