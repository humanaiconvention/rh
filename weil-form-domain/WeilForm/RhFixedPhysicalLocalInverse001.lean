import RhFixedPhysicalPulledSchur001
import RhNativeDilationSmallness001

/-! Local actual outward inversion from only the explicitly stated base
physical gap. The perturbation budget is supplied by the proved complete
native dilation theorem, not by an additional arithmetic premise. This does
not prove a gap exists or any outward Schur residual has the required sign. -/
set_option maxHeartbeats 0
noncomputable section
open Set MeasureTheory
open scoped Topology BigOperators
namespace RhFixedPhysicalLocalInverse
open RhWeightedMeasureEmbedding RhFlatSmoothCore RhPhysicalOrthogonalSchur
open RhPulledCompleteForm RhFixedPhysicalPulledSchur

theorem exists_local_control {d : ℕ} {R : ℝ} (hR : 0 < R)
    (C : ℝ) (N : ℕ) (p : Fin d → FlatCoreSpace R) {mu : ℝ}
    (hmu : 0 < mu) (hgap : PhysicalGap R C N p mu) :
    ∃ delta > 0, ∀ (r : ℝ) (hr : 1 ≤ r), |r - 1| < delta →
      Control hr C N p mu
        ((mu / (mu + RhCompleteFormBound.boundConstant R C N + 1)) / 2) := by
  have hK := RhCompleteFormBound.boundConstant_nonneg R C N
  have ht : 0 < mu / (mu + RhCompleteFormBound.boundConstant R C N + 1) := by
    positivity
  obtain ⟨delta, hdelta, hbudget⟩ :=
    RhNativeDilationSmallness.uniform_actual_graph_form_smallness hR C N
      (half_pos ht)
  refine ⟨delta, hdelta, ?_⟩
  intro r hr hclose
  refine ⟨hmu, hgap, ?_, by linarith⟩
  intro q
  have hb := hbudget r hr hclose (toCore R p q)
  simpa only [toCore_norm] using hb

/-- An actual bounded weak inverse on the FIXED physical orthogonal
complement exists for every sufficiently small outward dilation. -/
theorem exists_actual_local_inverse {d : ℕ} {R : ℝ} (hR : 0 < R)
    (C : ℝ) (N : ℕ) (p : Fin d → FlatCoreSpace R) {mu : ℝ}
    (hmu : 0 < mu) (hgap : PhysicalGap R C N p mu) :
    ∃ delta > 0, ∀ (r : ℝ) (hr : 1 ≤ r), |r - 1| < delta →
      ∃ T : ComplementSpace R p →L[ℝ] ComplementSpace R p,
        ∀ b q : ComplementSpace R p,
          pulledForm hr C N (toCore R p (T b)) (toCore R p q) = inner ℝ b q := by
  obtain ⟨delta, hdelta, hcontrol⟩ := exists_local_control hR C N p hmu hgap
  refine ⟨delta, hdelta, ?_⟩
  intro r hr hclose
  let hc := hcontrol r hr hclose
  refine ⟨RhFixedPhysicalPulledSchur.inverse hr C N p hc, ?_⟩
  exact RhFixedPhysicalPulledSchur.inverse_weak_equation hr C N p hc

end RhFixedPhysicalLocalInverse
#print axioms RhFixedPhysicalLocalInverse.exists_local_control
#print axioms RhFixedPhysicalLocalInverse.exists_actual_local_inverse