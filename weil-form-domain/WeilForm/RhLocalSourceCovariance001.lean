import RhActualSourceCovariance001
import RhFixedPhysicalLocalInverse001

/-! Local actual inverse covariance from an explicit BASE physical gap alone.
Both Control and the whole-source bound are produced by accepted native
arithmetic dilation estimates. Baseline zero-row equations are stated exactly.
This is local fixed-horizon control, not all-radius positivity.
-/
set_option maxHeartbeats 0
noncomputable section
open scoped Topology
namespace RhLocalSourceCovariance
open RhFlatSmoothCore RhPulledCompleteForm RhPhysicalOrthogonalSchur
open RhFixedPhysicalPulledSchur

/-- The only positivity hypothesis is the declared old physical complement
gap. The perturbation and source budgets are conclusions, not premises. -/
theorem exists_local_covariance_budget {d : ℕ} {R : ℝ} (hR : 0 < R)
    (C : ℝ) (N : ℕ) (p : Fin d → FlatCoreSpace R) {mu eps : ℝ}
    (hmu : 0 < mu) (hgap : PhysicalGap R C N p mu) (heps : 0 < eps) :
    ∃ delta > 0, ∀ (r : ℝ) (hr : 1 ≤ r), |r - 1| < delta →
      ∃ h : Control hr C N p mu
        ((mu / (mu + RhCompleteFormBound.boundConstant R C N + 1)) / 2),
      ∀ v w : FlatCoreSpace R,
      (∀ q : ComplementSpace R p, baseForm R C N v (toCore R p q) = 0) →
      (∀ q : ComplementSpace R p, baseForm R C N w (toCore R p q) = 0) →
      |inner ℝ (crossSource hr C N p v)
        (inverse hr C N p h (crossSource hr C N p w))| ≤
        eps ^ 2 * ‖v‖ * ‖w‖ /
          (mu / (mu + RhCompleteFormBound.boundConstant R C N + 1) -
            (mu / (mu + RhCompleteFormBound.boundConstant R C N + 1)) / 2) := by
  obtain ⟨d1, hd1, hc⟩ :=
    RhFixedPhysicalLocalInverse.exists_local_control hR C N p hmu hgap
  obtain ⟨d2, hd2, hb⟩ :=
    RhActualSourceCovariance.local_actual_covariance_budget hR C N heps
  refine ⟨min d1 d2, lt_min hd1 hd2, ?_⟩
  intro r hr hclose
  have h1 : |r - 1| < d1 := lt_of_lt_of_le hclose (min_le_left _ _)
  have h2 : |r - 1| < d2 := lt_of_lt_of_le hclose (min_le_right _ _)
  let h := hc r hr h1
  refine ⟨h, ?_⟩
  intro v w hv hw
  exact hb r hr h2 p h v w hv hw

/-- Local full residual budget, with the SAME inverse and every arithmetic
cross companion retained. No nonnegative residual conclusion is claimed. -/
theorem exists_local_residual_budget {d : ℕ} {R : ℝ} (hR : 0 < R)
    (C : ℝ) (N : ℕ) (p : Fin d → FlatCoreSpace R) {mu eps : ℝ}
    (hmu : 0 < mu) (hgap : PhysicalGap R C N p mu) (heps : 0 < eps) :
    ∃ delta > 0, ∀ (r : ℝ) (hr : 1 ≤ r), |r - 1| < delta →
      ∃ h : Control hr C N p mu
        ((mu / (mu + RhCompleteFormBound.boundConstant R C N + 1)) / 2),
      ∀ v : FlatCoreSpace R,
      (∀ q : ComplementSpace R p, baseForm R C N v (toCore R p q) = 0) →
      (pulledForm hr C N v v -
        eps ^ 2 * ‖v‖ ^ 2 /
          (mu / (mu + RhCompleteFormBound.boundConstant R C N + 1) -
            (mu / (mu + RhCompleteFormBound.boundConstant R C N + 1)) / 2) ≤
        RhFixedPhysicalPulledSchur.residual hr C N p h v ∧
      RhFixedPhysicalPulledSchur.residual hr C N p h v ≤ pulledForm hr C N v v) := by
  obtain ⟨d1, hd1, hc⟩ :=
    RhFixedPhysicalLocalInverse.exists_local_control hR C N p hmu hgap
  obtain ⟨d2, hd2, hb⟩ :=
    RhNativeBilinearSmallness.uniform_actual_bilinear_smallness hR C N heps
  refine ⟨min d1 d2, lt_min hd1 hd2, ?_⟩
  intro r hr hclose
  have h1 : |r - 1| < d1 := lt_of_lt_of_le hclose (min_le_left _ _)
  have h2 : |r - 1| < d2 := lt_of_lt_of_le hclose (min_le_right _ _)
  let h := hc r hr h1
  refine ⟨h, ?_⟩
  intro v hv
  exact RhActualSourceCovariance.actual_residual_budget hr C N p h heps.le
    (hb r hr h2) v hv

end RhLocalSourceCovariance
#print axioms RhLocalSourceCovariance.exists_local_covariance_budget
#print axioms RhLocalSourceCovariance.exists_local_residual_budget
