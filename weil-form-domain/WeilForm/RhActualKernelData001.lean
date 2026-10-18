import RhNativePhysicalKernelBasis001
import RhPulledCompleteForm001

/-! A single honest native interface for the actual nullspace data needed by
Schur assembly. Base positivity is explicit; outward positivity is not asserted. -/
noncomputable section
open Set MeasureTheory
open scoped Topology BigOperators
namespace RhActualKernelData
open RhWeightedMeasureEmbedding RhNativeCompleteBilinear RhFlatSmoothCore
open RhPulledCompleteForm RhNativePhysicalKernelBasis

theorem exists_actual_kernel_data {R : ℝ} (hR : 0 < R) (C : ℝ) (N : ℕ)
    (hpos : ∀ x : FlatCoreSpace R,
      0 ≤ completeForm R C N (x : WeightedSpace) (x : WeightedSpace)) :
    ∃ (d : ℕ) (p : Fin d → FlatCoreSpace R) (mu : ℝ),
      Orthonormal ℝ (fun i => physicalEmbedding (p i : WeightedSpace)) ∧
      (∀ i, p i ∈ (baseForm R C N).ker) ∧
      (∀ z : FlatCoreSpace R, z ∈ (baseForm R C N).ker →
        ∃ c : Fin d → ℝ, z = ∑ i, c i • p i) ∧
      0 < mu ∧ RhPhysicalOrthogonalSchur.PhysicalGap R C N p mu := by
  obtain ⟨mu,hmu,hgap⟩ := actual_physical_gap hR C N hpos
  refine ⟨imageDimension R C N, family hR C N hpos, mu,
    family_physical_orthonormal hR C N hpos, ?_, ?_, hmu, hgap⟩
  · exact family_mem_kernel hR C N hpos
  · exact kernel_spanning hR C N hpos

end RhActualKernelData
#print axioms RhActualKernelData.exists_actual_kernel_data
