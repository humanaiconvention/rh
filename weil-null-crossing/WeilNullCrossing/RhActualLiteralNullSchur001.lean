import RhActualKernelData001
import RhActualRotatingLocalControl001
import RhOldNullPhysicalIsometry001
import RhLiteralZeroBlockSchur001

/-! Literal old-physical-nullspace Schur reduction. Actual base positivity
constructs the finite radical and its physical gap. Its inward pullback is a
moving orthonormal family, and actual local complement control is constructed.
The full low block is exactly zero. No arithmetic cross-source vanishing,
nonvanishing, outward positivity, or actual zero-radius is asserted. -/
set_option maxHeartbeats 150000
set_option synthInstance.maxHeartbeats 20000
noncomputable section
open Set MeasureTheory
open scoped Topology BigOperators
namespace RhActualLiteralNullSchur
open RhWeightedMeasureEmbedding RhFlatSmoothCore RhNativeCompleteBilinear
open RhPhysicalOrthogonalSchur RhPulledCompleteForm RhFixedPhysicalPulledSchur
open RhFixedPhysicalSchurMatrix RhInwardOldNullLift

/-- The projection is onto literal old physical vectors after outward
transport, rather than the dilated old basis. All sources are FULL rows. -/
theorem local_literal_null_schur_target {R : ℝ} (hR : 0 < R) (C : ℝ) (N : ℕ)
    (hpos : ∀ F : FlatCoreSpace R,
      0 ≤ completeForm R C N (F : WeightedSpace) (F : WeightedSpace)) :
    ∃ (d : ℕ) (p : Fin d → FlatCoreSpace R) (mu : ℝ),
      Orthonormal ℝ (fun i => physicalEmbedding (p i : WeightedSpace)) ∧
      (∀ i, p i ∈ (baseForm R C N).ker) ∧
      (∀ z : FlatCoreSpace R, z ∈ (baseForm R C N).ker →
        ∃ c : Fin d → ℝ, z = ∑ i, c i • p i) ∧
      0 < mu ∧ PhysicalGap R C N p mu ∧
      ∃ delta > 0, ∀ (r : ℝ) (hr : 1 ≤ r), |r-1| < delta →
        let w : Fin d → FlatCoreSpace R := fun i => oldNullLift hR hr (p i)
        ∃ h : Control hr C N w (mu/2)
          ((((mu/2) / (mu/2 + RhCompleteFormBound.boundConstant R C N + 1))) / 2),
          (∀ i j, pulledForm hr C N (w i) (w j) = 0) ∧
          (∀ i j, schurMatrix hr C N w h i j =
            - inner ℝ (crossSource hr C N w (w i))
              (inverse hr C N w h (crossSource hr C N w (w j)))) ∧
          (∀ c : Fin d → ℝ,
            ∑ i, ∑ j, c i * c j * schurMatrix hr C N w h i j ≤ 0) ∧
          ((∀ F : FlatCoreSpace R, 0 ≤ pulledForm hr C N F F) ↔
            ∀ i, crossSource hr C N w (w i) = 0) := by
  obtain ⟨d,p,mu,hp,hn,hspan,hmu,hgap⟩ :=
    RhActualKernelData.exists_actual_kernel_data hR C N hpos
  obtain ⟨delta,hdelta,hlocal⟩ :=
    RhActualRotatingLocalControl.exists_actual_local_control hR C N p hp hn hmu hgap
  refine ⟨d,p,mu,hp,hn,hspan,hmu,hgap,delta,hdelta,?_⟩
  intro r hr hclose
  let w : Fin d → FlatCoreSpace R := fun i => oldNullLift hR hr (p i)
  have h : Control hr C N w (mu/2)
      ((((mu/2) / (mu/2 + RhCompleteFormBound.boundConstant R C N + 1))) / 2) :=
    hlocal r hr hclose
  have hw : Orthonormal ℝ (fun i => physicalEmbedding (w i : WeightedSpace)) :=
    RhOldNullPhysicalIsometry.physical_orthonormal hR hr p hp
  have hzero (i j : Fin d) : pulledForm hr C N (w i) (w j) = 0 := by
    change pulledForm hr C N (oldNullLift hR hr (p i)) (oldNullLift hR hr (p j)) = 0
    rw [pulledForm_oldNullLift_pair hR hr C N]
    have hz := hn i
    change baseForm R C N (p i) = 0 at hz
    have hj := congrArg (fun T : FlatCoreSpace R →L[ℝ] ℝ => T (p j)) hz
    simpa only [ContinuousLinearMap.zero_apply] using hj
  refine ⟨h,hzero,?_,?_,?_⟩
  · exact RhLiteralZeroBlockSchur.schur_entry hr C N w h hzero
  · exact RhLiteralZeroBlockSchur.schur_quadratic_nonpositive hr C N w h hzero
  · exact RhLiteralZeroBlockSchur.full_core_nonnegative_iff_full_sources_zero
      hr C N w hw h hzero

end RhActualLiteralNullSchur
#print axioms RhActualLiteralNullSchur.local_literal_null_schur_target
