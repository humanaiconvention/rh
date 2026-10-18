import RhActualNullSchurTarget001
import RhActualKernelData001
import RhSchurMatrixZero001

/-! Terminal local reduction from actual base positivity ALONE. The actual
physical nullspace basis, finite dimension, positive complement gap, local
projection surjectivity and complement inverse are constructed. The remaining
arithmetic condition is literal Schur MATRIX ZERO, not a positive margin.
No matrix entry is asserted to vanish or to be nonzero. -/
set_option maxHeartbeats 100000
set_option synthInstance.maxHeartbeats 20000
noncomputable section
open Set MeasureTheory Filter
open scoped Topology BigOperators
namespace RhBasePositiveSchurReduction
open RhWeightedMeasureEmbedding RhNativeCompleteBilinear RhFlatSmoothCore
open RhPhysicalOrthogonalSchur RhPulledCompleteForm RhFixedPhysicalPulledSchur
open RhFixedPhysicalSchurMatrix RhActualNullSchurTarget RhSchurMatrixZero

theorem local_complete_schur_zero_target {R : ℝ} (hR : 0 < R) (C : ℝ) (N : ℕ)
    (hpos : ∀ F : FlatCoreSpace R,
      0 ≤ completeForm R C N (F : WeightedSpace) (F : WeightedSpace)) :
    ∃ (d : ℕ) (p : Fin d → FlatCoreSpace R) (mu : ℝ),
      Orthonormal ℝ (fun i => physicalEmbedding (p i : WeightedSpace)) ∧
      (∀ i, p i ∈ (baseForm R C N).ker) ∧
      (∀ z : FlatCoreSpace R, z ∈ (baseForm R C N).ker →
        ∃ c : Fin d → ℝ, z = ∑ i, c i • p i) ∧
      0 < mu ∧ PhysicalGap R C N p mu ∧
      ∃ delta > 0, ∀ (r : ℝ) (hr : 1 ≤ r), |r - 1| < delta →
        ∃ h : Control hr C N p mu
          ((mu / (mu + RhCompleteFormBound.boundConstant R C N + 1)) / 2),
          (∀ c : Fin d → ℝ,
            ∑ i, ∑ j, c i * c j * schurMatrix hr C N p h i j ≤ 0) ∧
            ((∀ F : FlatCoreSpace R, 0 ≤ pulledForm hr C N F F) ↔
              schurMatrix hr C N p h = 0) := by
  obtain ⟨d, p, mu, hp, hn, hspan, hmu, hgap⟩ :=
    RhActualKernelData.exists_actual_kernel_data hR C N hpos
  obtain ⟨delta, hdelta, hlocal⟩ :=
    exists_local_actual_null_schur_target hR C N p hp hn hmu hgap
  refine ⟨d, p, mu, hp, hn, hspan, hmu, hgap, delta, hdelta, ?_⟩
  intro r hr hclose
  obtain ⟨h, hnonpos, hcriterion⟩ := hlocal r hr hclose
  refine ⟨h, hnonpos, ?_⟩
  exact hcriterion.trans (schurMatrix_zero_iff hr C N p h).symm

end RhBasePositiveSchurReduction
#print axioms RhBasePositiveSchurReduction.local_complete_schur_zero_target