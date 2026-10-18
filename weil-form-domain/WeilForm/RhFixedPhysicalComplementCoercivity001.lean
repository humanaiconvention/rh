import RhFixedPhysicalComplementGeometry001

/-! Actual fixed-physical-complement coercivity from the explicit base physical
gap and the literal q_r-q_1 graph budget. No inverse or residual sign is assumed. -/
set_option maxHeartbeats 100000
set_option synthInstance.maxHeartbeats 20000
noncomputable section
open Set MeasureTheory
open scoped Topology BigOperators
namespace RhFixedPhysicalPulledSchur
open RhWeightedMeasureEmbedding RhFlatSmoothCore RhNativeCompleteBilinear
open RhPhysicalOrthogonalSchur RhPulledCompleteForm

def pulledComplement {d : ℕ} {R r : ℝ} (hr : 1 ≤ r) (C : ℝ) (N : ℕ)
    (p : Fin d → FlatCoreSpace R) :
    ComplementSpace R p →L[ℝ] ComplementSpace R p →L[ℝ] ℝ :=
  (pulledForm hr C N).bilinearComp (toCore R p) (toCore R p)

lemma pulledComplement_apply {d : ℕ} {R r : ℝ} (hr : 1 ≤ r) (C : ℝ) (N : ℕ)
    (p : Fin d → FlatCoreSpace R) (q z : ComplementSpace R p) :
    pulledComplement hr C N p q z =
      pulledForm hr C N (toCore R p q) (toCore R p z) := rfl

theorem pulled_equals_base_add_difference {d : ℕ} {R r : ℝ} (hr : 1 ≤ r)
    (C : ℝ) (N : ℕ) (p : Fin d → FlatCoreSpace R)
    (q z : ComplementSpace R p) :
    pulledComplement hr C N p q z = form R C N p q z +
      differenceForm hr C N (toCore R p q) (toCore R p z) := by
  rw [pulledComplement_apply, differenceForm_apply, baseForm_apply,
    toCore_ambient, toCore_ambient, form_apply]
  ring

structure Control {d : ℕ} {R r : ℝ} (hr : 1 ≤ r) (C : ℝ) (N : ℕ)
    (p : Fin d → FlatCoreSpace R) (mu eta : ℝ) : Prop where
  positive_mu : 0 < mu
  base_gap : PhysicalGap R C N p mu
  perturbation : ∀ q : ComplementSpace R p,
    |differenceForm hr C N (toCore R p q) (toCore R p q)| ≤ eta * ‖q‖ ^ 2
  smaller : eta < mu / (mu + RhCompleteFormBound.boundConstant R C N + 1)

theorem base_graph_gap {d : ℕ} {R r : ℝ} (hr : 1 ≤ r) (C : ℝ) (N : ℕ)
    (p : Fin d → FlatCoreSpace R) {mu eta : ℝ} (h : Control hr C N p mu eta)
    (q : ComplementSpace R p) :
    (mu / (mu + RhCompleteFormBound.boundConstant R C N + 1)) * ‖q‖ ^ 2 ≤
      form R C N p q q := by
  have hg := RhNativeGraphCoercivity.complete_graph_gap R C N h.positive_mu
    (q : WeightedSpace) (h.base_gap q)
  simpa only [Submodule.norm_coe, form_apply] using hg

/-- Exact remaining graph gap, with no radius-uniform assertion. -/
theorem outward_graph_gap {d : ℕ} {R r : ℝ} (hr : 1 ≤ r) (C : ℝ) (N : ℕ)
    (p : Fin d → FlatCoreSpace R) {mu eta : ℝ} (h : Control hr C N p mu eta)
    (q : ComplementSpace R p) :
    (mu / (mu + RhCompleteFormBound.boundConstant R C N + 1) - eta) * ‖q‖ ^ 2 ≤
      pulledComplement hr C N p q q := by
  have hb := base_graph_gap hr C N p h q
  have hd := (abs_le.mp (h.perturbation q)).1
  rw [pulled_equals_base_add_difference]
  nlinarith

theorem pulled_isCoercive {d : ℕ} {R r : ℝ} (hr : 1 ≤ r) (C : ℝ) (N : ℕ)
    (p : Fin d → FlatCoreSpace R) {mu eta : ℝ} (h : Control hr C N p mu eta) :
    IsCoercive (pulledComplement hr C N p) := by
  refine ⟨mu / (mu + RhCompleteFormBound.boundConstant R C N + 1) - eta,
    sub_pos.mpr h.smaller, ?_⟩
  intro q
  simpa only [pow_two, mul_assoc] using outward_graph_gap hr C N p h q

theorem pulled_symmetric {d : ℕ} {R r : ℝ} (hr : 1 ≤ r) (C : ℝ) (N : ℕ)
    (p : Fin d → FlatCoreSpace R) (q z : ComplementSpace R p) :
    pulledComplement hr C N p q z = pulledComplement hr C N p z q := by
  rw [pulledComplement_apply, pulledComplement_apply]
  exact pulledForm_symmetric hr C N (toCore R p q) (toCore R p z)

end RhFixedPhysicalPulledSchur
#print axioms RhFixedPhysicalPulledSchur.pulled_equals_base_add_difference
#print axioms RhFixedPhysicalPulledSchur.pulled_isCoercive
#print axioms RhFixedPhysicalPulledSchur.outward_graph_gap