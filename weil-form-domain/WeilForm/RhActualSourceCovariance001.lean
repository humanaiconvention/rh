import RhPerturbationSource001
import RhInverseCovarianceBudget001
import RhFixedPhysicalPulledSchur001

/-! Actual whole-source covariance for the SAME outward native inverse.
The old row-zero equation and the base physical gap remain explicit. Local
source smallness is proved by the arithmetic dilation theorem, not assumed.
No residual sign is inferred from the quadratic loss budget.
-/
set_option maxHeartbeats 0
noncomputable section
open scoped Topology
namespace RhActualSourceCovariance
open RhFlatSmoothCore RhPulledCompleteForm RhPhysicalOrthogonalSchur
open RhFixedPhysicalPulledSchur

lemma crossSource_eq_perturbation {d : ℕ} {R r : ℝ} (hr : 1 ≤ r)
    (C : ℝ) (N : ℕ) (p : Fin d → FlatCoreSpace R) (v : FlatCoreSpace R)
    (hzero : ∀ q : ComplementSpace R p, baseForm R C N v (toCore R p q) = 0) :
    crossSource hr C N p v = RhPerturbationSource.source hr C N p v := by
  apply ext_inner_right ℝ
  intro q
  rw [RhFixedPhysicalPulledSchur.crossSource_weak,
    RhPerturbationSource.source_is_outward_on_zero_row hr C N p v hzero q]

/-- Full mixed covariance, retaining every native companion in each source
and one common actual inverse. No termwise inverse or covariance is used. -/
theorem actual_mixed_covariance_bound {d : ℕ} {R r : ℝ} (hr : 1 ≤ r)
    (C : ℝ) (N : ℕ) (p : Fin d → FlatCoreSpace R)
    {mu eta eps : ℝ} (h : Control hr C N p mu eta) (heps : 0 ≤ eps)
    (hbound : ∀ F G : FlatCoreSpace R,
      |differenceForm hr C N F G| ≤ eps * ‖F‖ * ‖G‖)
    (v w : FlatCoreSpace R)
    (hv : ∀ q : ComplementSpace R p, baseForm R C N v (toCore R p q) = 0)
    (hw : ∀ q : ComplementSpace R p, baseForm R C N w (toCore R p q) = 0) :
    |inner ℝ (crossSource hr C N p v)
      (inverse hr C N p h (crossSource hr C N p w))| ≤
      eps ^ 2 * ‖v‖ * ‖w‖ /
        (mu / (mu + RhCompleteFormBound.boundConstant R C N + 1) - eta) := by
  rw [crossSource_eq_perturbation hr C N p v hv,
    crossSource_eq_perturbation hr C N p w hw]
  exact RhInverseCovarianceBudget.quadratic_covariance_bound
    (pulledComplement hr C N p) (pulled_isCoercive hr C N p h)
    (sub_pos.mpr h.smaller) heps (norm_nonneg v) (norm_nonneg w)
    (outward_graph_gap hr C N p h)
    (RhPerturbationSource.source hr C N p v)
    (RhPerturbationSource.source hr C N p w)
    (RhPerturbationSource.source_norm_bound hr C N p heps hbound v)
    (RhPerturbationSource.source_norm_bound hr C N p heps hbound w)

/-- The all-component residual is trapped by the actual outward diagonal
and its quadratic whole-source inverse cost. Neither endpoint is asserted
nonnegative. -/
theorem actual_residual_budget {d : ℕ} {R r : ℝ} (hr : 1 ≤ r)
    (C : ℝ) (N : ℕ) (p : Fin d → FlatCoreSpace R)
    {mu eta eps : ℝ} (h : Control hr C N p mu eta) (heps : 0 ≤ eps)
    (hbound : ∀ F G : FlatCoreSpace R,
      |differenceForm hr C N F G| ≤ eps * ‖F‖ * ‖G‖)
    (v : FlatCoreSpace R)
    (hv : ∀ q : ComplementSpace R p, baseForm R C N v (toCore R p q) = 0) :
    pulledForm hr C N v v -
      eps ^ 2 * ‖v‖ ^ 2 /
        (mu / (mu + RhCompleteFormBound.boundConstant R C N + 1) - eta) ≤
      residual hr C N p h v ∧
    residual hr C N p h v ≤ pulledForm hr C N v v := by
  have hpay := actual_mixed_covariance_bound hr C N p h heps hbound v v hv hv
  have hnonneg := payment_nonnegative hr C N p h v
  rw [abs_of_nonneg hnonneg] at hpay
  have hnum : eps ^ 2 * ‖v‖ * ‖v‖ = eps ^ 2 * ‖v‖ ^ 2 := by ring
  rw [hnum] at hpay
  constructor <;> unfold RhFixedPhysicalPulledSchur.residual <;> linarith

/-- No local source-bound premise: full signed native bilinear smallness
produces the covariance budget. Actual inverse existence remains encoded by
Control; local derivation of Control from the base gap is a separate theorem. -/
theorem local_actual_covariance_budget {R : ℝ} (hR : 0 < R) (C : ℝ) (N : ℕ)
    {eps : ℝ} (heps : 0 < eps) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ (r : ℝ) (hr : 1 ≤ r), |r - 1| < delta →
      ∀ {d : ℕ} (p : Fin d → FlatCoreSpace R) {mu eta : ℝ}
        (h : Control hr C N p mu eta) (v w : FlatCoreSpace R),
      (∀ q : ComplementSpace R p, baseForm R C N v (toCore R p q) = 0) →
      (∀ q : ComplementSpace R p, baseForm R C N w (toCore R p q) = 0) →
      |inner ℝ (crossSource hr C N p v)
        (inverse hr C N p h (crossSource hr C N p w))| ≤
        eps ^ 2 * ‖v‖ * ‖w‖ /
          (mu / (mu + RhCompleteFormBound.boundConstant R C N + 1) - eta) := by
  obtain ⟨delta, hdelta, hd⟩ :=
    RhNativeBilinearSmallness.uniform_actual_bilinear_smallness hR C N heps
  refine ⟨delta, hdelta, ?_⟩
  intro r hr hclose d p mu eta h v w hv hw
  exact actual_mixed_covariance_bound hr C N p h heps.le (hd r hr hclose) v w hv hw

end RhActualSourceCovariance
#print axioms RhActualSourceCovariance.crossSource_eq_perturbation
#print axioms RhActualSourceCovariance.actual_mixed_covariance_bound
#print axioms RhActualSourceCovariance.actual_residual_budget
#print axioms RhActualSourceCovariance.local_actual_covariance_budget

