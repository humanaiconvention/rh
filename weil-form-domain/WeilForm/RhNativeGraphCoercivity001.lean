import RhNativeBoundedPartControl001
import RhCoerciveSchurInverse001

/-! Convert a PHYSICAL L2 gap for the actual complete arithmetic form into
coercivity in its actual complete weighted graph norm. The physical gap is an
explicit, still arithmetic hypothesis; the norm conversion and bounded-part
constant are proved. No nullspace, gap, positivity or inverse is assumed away. -/
set_option maxHeartbeats 0
noncomputable section
open MeasureTheory
open scoped Topology
namespace RhNativeGraphCoercivity
open RhWeightedMeasureEmbedding RhNativeCompleteBilinear

lemma scalar_gap_conversion {a g m K mu : ℝ} (hmu : 0 < mu) (hK : 0 ≤ K)
    (hgraph : g ≤ a + (K + 1) * m) (hgap : mu * m ≤ a) :
    mu / (mu + K + 1) * g ≤ a := by
  have hden : 0 < mu + K + 1 := by positivity
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hden).mpr
  have h1 := mul_le_mul_of_nonneg_left hgraph hmu.le
  have h2 := mul_le_mul_of_nonneg_left hgap (by positivity : 0 ≤ K + 1)
  nlinarith

/-- The actual complete graph norm is controlled by the actual complete form
plus the proved native bounded-part mass budget. -/
theorem native_graph_control (R C : ℝ) (N : ℕ) (F : WeightedSpace) :
    ‖F‖ ^ 2 ≤ completeForm R C N F F +
      (RhCompleteFormBound.boundConstant R C N + 1) * ‖physicalEmbedding F‖ ^ 2 := by
  have hb := RhNativeBoundedPartControl.boundedPart_mass_bound R C N F
  have hlo := (abs_le.mp hb).1
  change ‖F‖ ^ 2 ≤ archPair F F + boundedPart R C N F F +
    (RhCompleteFormBound.boundConstant R C N + 1) * ‖physicalEmbedding F‖ ^ 2
  rw [archPair_apply, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
  nlinarith

/-- A physical spectral gap implies a graph-norm gap with an explicit genuine
coefficient. No graph-coercivity conclusion is included among the premises. -/
theorem complete_graph_gap (R C : ℝ) (N : ℕ) {mu : ℝ} (hmu : 0 < mu)
    (F : WeightedSpace)
    (hgap : mu * ‖physicalEmbedding F‖ ^ 2 ≤ completeForm R C N F F) :
    (mu / (mu + RhCompleteFormBound.boundConstant R C N + 1)) * ‖F‖ ^ 2 ≤
      completeForm R C N F F :=
  scalar_gap_conversion hmu (RhCompleteFormBound.boundConstant_nonneg R C N)
    (native_graph_control R C N F) hgap

/-- Restriction to any declared subspace uses the exact actual form, unchanged. -/
def restrictedForm (R C : ℝ) (N : ℕ) (S : Submodule ℝ WeightedSpace) :
    S →L[ℝ] S →L[ℝ] ℝ :=
  (completeForm R C N).bilinearComp S.subtypeL S.subtypeL

/-- This is the precise interface needed by Lax-Milgram on a complete closed
complement. Existence of the PHYSICAL gap on that complement remains open. -/
theorem restricted_isCoercive_of_physical_gap (R C : ℝ) (N : ℕ)
    (S : Submodule ℝ WeightedSpace) {mu : ℝ} (hmu : 0 < mu)
    (hgap : ∀ q : S, mu * ‖physicalEmbedding (q : WeightedSpace)‖ ^ 2 ≤
      completeForm R C N (q : WeightedSpace) (q : WeightedSpace)) :
    IsCoercive (restrictedForm R C N S) := by
  refine ⟨mu / (mu + RhCompleteFormBound.boundConstant R C N + 1), by
    have hK := RhCompleteFormBound.boundConstant_nonneg R C N
    positivity, ?_⟩
  intro q
  have h := complete_graph_gap R C N hmu (q : WeightedSpace) (hgap q)
  change (mu / (mu + RhCompleteFormBound.boundConstant R C N + 1)) * ‖q‖ * ‖q‖ ≤
    completeForm R C N (q : WeightedSpace) (q : WeightedSpace)
  simpa only [Submodule.norm_coe, pow_two, mul_assoc] using h

/-- The constructed real smooth core inherits the same concrete graph-norm
lower bound. This is a quadratic inequality, not a declared operator inverse. -/
theorem core_graph_gap (R C : ℝ) (N : ℕ) {mu : ℝ} (hmu : 0 < mu)
    (q : RhClosedSmoothCore.CoreSpace R)
    (hgap : mu * ‖physicalEmbedding (coreInclusion R q)‖ ^ 2 ≤
      completeForm R C N (coreInclusion R q) (coreInclusion R q)) :
    (mu / (mu + RhCompleteFormBound.boundConstant R C N + 1)) * ‖q‖ ^ 2 ≤
      completeForm R C N (coreInclusion R q) (coreInclusion R q) := by
  have h := complete_graph_gap R C N hmu (coreInclusion R q) hgap
  exact h
end RhNativeGraphCoercivity
#print axioms RhNativeGraphCoercivity.native_graph_control
#print axioms RhNativeGraphCoercivity.complete_graph_gap
#print axioms RhNativeGraphCoercivity.restricted_isCoercive_of_physical_gap
#print axioms RhNativeGraphCoercivity.core_graph_gap
