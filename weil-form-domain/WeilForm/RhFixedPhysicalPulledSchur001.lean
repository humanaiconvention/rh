import RhFixedPhysicalComplementCoercivity001

/-! Actual fixed-P outward Schur inverse and residual. Base physical gap and
literal perturbation budget remain explicit; inverse is constructed. -/
set_option maxHeartbeats 100000
set_option synthInstance.maxHeartbeats 20000
noncomputable section
open Set MeasureTheory
open scoped Topology BigOperators
namespace RhFixedPhysicalPulledSchur
open RhWeightedMeasureEmbedding RhFlatSmoothCore RhNativeCompleteBilinear
open RhPhysicalOrthogonalSchur RhPulledCompleteForm
def inverse {d : ℕ} {R r : ℝ} (hr : 1 ≤ r) (C : ℝ) (N : ℕ)
    (p : Fin d → FlatCoreSpace R) {mu eta : ℝ} (h : Control hr C N p mu eta) :
    ComplementSpace R p →L[ℝ] ComplementSpace R p :=
  RhCoerciveSchurInverse.inverse (pulledComplement hr C N p) (pulled_isCoercive hr C N p h)

theorem inverse_weak_equation {d : ℕ} {R r : ℝ} (hr : 1 ≤ r) (C : ℝ) (N : ℕ)
    (p : Fin d → FlatCoreSpace R) {mu eta : ℝ} (h : Control hr C N p mu eta)
    (b q : ComplementSpace R p) :
    pulledForm hr C N (toCore R p (inverse hr C N p h b)) (toCore R p q) =
      inner ℝ b q :=
  RhCoerciveSchurInverse.inverse_weak_equation
    (pulledComplement hr C N p) (pulled_isCoercive hr C N p h) b q

/-- Riesz representative of the complete actual OUTWARD cross functional,
on the fixed physical complement, including all dilation companions. -/
def crossSource {d : ℕ} {R r : ℝ} (hr : 1 ≤ r) (C : ℝ) (N : ℕ)
    (p : Fin d → FlatCoreSpace R) (v : FlatCoreSpace R) : ComplementSpace R p :=
  (InnerProductSpace.toDual ℝ (ComplementSpace R p)).symm
    ((pulledForm hr C N v).comp (toCore R p))

theorem crossSource_weak {d : ℕ} {R r : ℝ} (hr : 1 ≤ r) (C : ℝ) (N : ℕ)
    (p : Fin d → FlatCoreSpace R) (v : FlatCoreSpace R) (q : ComplementSpace R p) :
    inner ℝ (crossSource hr C N p v) q = pulledForm hr C N v (toCore R p q) :=
  InnerProductSpace.toDual_symm_apply

def residual {d : ℕ} {R r : ℝ} (hr : 1 ≤ r) (C : ℝ) (N : ℕ)
    (p : Fin d → FlatCoreSpace R) {mu eta : ℝ} (h : Control hr C N p mu eta)
    (v : FlatCoreSpace R) : ℝ :=
  pulledForm hr C N v v -
    inner ℝ (crossSource hr C N p v)
      (inverse hr C N p h (crossSource hr C N p v))

lemma whole_form_expansion {d : ℕ} {R r : ℝ} (hr : 1 ≤ r) (C : ℝ) (N : ℕ)
    (p : Fin d → FlatCoreSpace R) (v : FlatCoreSpace R) (q : ComplementSpace R p) :
    pulledForm hr C N (v + toCore R p q) (v + toCore R p q) =
      pulledForm hr C N v v + 2 * inner ℝ (crossSource hr C N p v) q +
        pulledComplement hr C N p q q := by
  simp only [map_add, ContinuousLinearMap.add_apply]
  rw [pulledForm_symmetric hr C N (toCore R p q) v, crossSource_weak]
  change _ = pulledForm hr C N v v + 2 * pulledForm hr C N v (toCore R p q) +
    pulledForm hr C N (toCore R p q) (toCore R p q)
  ring

/-- The requested fixed-domain outward Schur condition, with an ACTUAL
constructed inverse. The residual sign is deliberately not asserted. -/
theorem actual_schur_iff {d : ℕ} {R r : ℝ} (hr : 1 ≤ r) (C : ℝ) (N : ℕ)
    (p : Fin d → FlatCoreSpace R) {mu eta : ℝ} (h : Control hr C N p mu eta)
    (v : FlatCoreSpace R) :
    (∀ q : ComplementSpace R p,
      0 ≤ pulledForm hr C N (v + toCore R p q) (v + toCore R p q)) ↔
      0 ≤ residual hr C N p h v := by
  simp only [whole_form_expansion]
  exact RhCoerciveSchurInverse.nonnegative_iff_residual
    (pulledComplement hr C N p) (pulled_isCoercive hr C N p h)
    (pulled_symmetric hr C N p) (pulledForm hr C N v v) (crossSource hr C N p v)

theorem payment_nonnegative {d : ℕ} {R r : ℝ} (hr : 1 ≤ r) (C : ℝ) (N : ℕ)
    (p : Fin d → FlatCoreSpace R) {mu eta : ℝ} (h : Control hr C N p mu eta)
    (v : FlatCoreSpace R) :
    0 ≤ inner ℝ (crossSource hr C N p v)
      (inverse hr C N p h (crossSource hr C N p v)) :=
  RhCoerciveSchurInverse.cross_payment_nonnegative
    (pulledComplement hr C N p) (pulled_isCoercive hr C N p h) _

theorem payment_le {d : ℕ} {R r : ℝ} (hr : 1 ≤ r) (C : ℝ) (N : ℕ)
    (p : Fin d → FlatCoreSpace R) {mu eta : ℝ} (h : Control hr C N p mu eta)
    (v : FlatCoreSpace R) :
    inner ℝ (crossSource hr C N p v)
      (inverse hr C N p h (crossSource hr C N p v)) ≤
        ‖crossSource hr C N p v‖ ^ 2 /
          (mu / (mu + RhCompleteFormBound.boundConstant R C N + 1) - eta) :=
  RhCoerciveSchurInverse.cross_payment_le
    (pulledComplement hr C N p) (pulled_isCoercive hr C N p h)
    (sub_pos.mpr h.smaller) (outward_graph_gap hr C N p h) _
end RhFixedPhysicalPulledSchur
#print axioms RhFixedPhysicalPulledSchur.inverse_weak_equation
#print axioms RhFixedPhysicalPulledSchur.actual_schur_iff
#print axioms RhFixedPhysicalPulledSchur.payment_nonnegative
#print axioms RhFixedPhysicalPulledSchur.payment_le