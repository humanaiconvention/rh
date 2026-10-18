import RhNativeBilinearSmallness001
import RhFixedPhysicalComplementGeometry001

/-! Actual Riesz source of the COMPLETE native perturbation on a fixed
physical-L2 complement. Uniform local source control is proved from actual
bilinear smallness. A baseline zero-row equation is explicit, never assumed
as a property of a chosen finite family.
-/
set_option maxHeartbeats 0
noncomputable section
open Set MeasureTheory
open scoped Topology
namespace RhPerturbationSource
open RhWeightedMeasureEmbedding RhFlatSmoothCore RhPulledCompleteForm
open RhPhysicalOrthogonalSchur RhFixedPhysicalPulledSchur

def source {d : ℕ} {R r : ℝ} (hr : 1 ≤ r) (C : ℝ) (N : ℕ)
    (p : Fin d → FlatCoreSpace R) (v : FlatCoreSpace R) : ComplementSpace R p :=
  (InnerProductSpace.toDual ℝ (ComplementSpace R p)).symm
    ((differenceForm hr C N v).comp (toCore R p))

lemma source_weak {d : ℕ} {R r : ℝ} (hr : 1 ≤ r) (C : ℝ) (N : ℕ)
    (p : Fin d → FlatCoreSpace R) (v : FlatCoreSpace R) (q : ComplementSpace R p) :
    inner ℝ (source hr C N p v) q = differenceForm hr C N v (toCore R p q) :=
  InnerProductSpace.toDual_symm_apply

/-- The actual complete source, provided the explicitly stated old row is
zero on the fixed complement. This is not a claim that the row is null. -/
lemma source_is_outward_on_zero_row {d : ℕ} {R r : ℝ} (hr : 1 ≤ r) (C : ℝ) (N : ℕ)
    (p : Fin d → FlatCoreSpace R) (v : FlatCoreSpace R)
    (hzero : ∀ q : ComplementSpace R p, baseForm R C N v (toCore R p q) = 0)
    (q : ComplementSpace R p) :
    inner ℝ (source hr C N p v) q = pulledForm hr C N v (toCore R p q) := by
  rw [source_weak, differenceForm_apply, hzero q, sub_zero]

lemma source_norm_bound {d : ℕ} {R r : ℝ} (hr : 1 ≤ r) (C : ℝ) (N : ℕ)
    (p : Fin d → FlatCoreSpace R) {eta : ℝ} (heta : 0 ≤ eta)
    (hbound : ∀ F G : FlatCoreSpace R, |differenceForm hr C N F G| ≤ eta * ‖F‖ * ‖G‖)
    (v : FlatCoreSpace R) : ‖source hr C N p v‖ ≤ eta * ‖v‖ := by
  let b := source hr C N p v
  have h := hbound v (toCore R p b)
  rw [toCore_norm, ← source_weak hr C N p v b] at h
  change |inner ℝ b b| ≤ eta * ‖v‖ * ‖b‖ at h
  rw [real_inner_self_eq_norm_sq, abs_of_nonneg (sq_nonneg _)] at h
  change ‖b‖ ≤ eta * ‖v‖
  by_cases hz : ‖b‖ = 0
  · rw [hz]
    exact mul_nonneg heta (norm_nonneg v)
  · have hp : 0 < ‖b‖ := lt_of_le_of_ne (norm_nonneg b) (Ne.symm hz)
    apply (mul_le_mul_iff_right₀ hp).mp
    nlinarith

/-- Locally the source estimate has NO perturbation-bound premise. It holds
uniformly over all finite families and all rows v on the actual real core. -/
theorem local_actual_source_norm {R : ℝ} (hR : 0 < R) (C : ℝ) (N : ℕ)
    {eta : ℝ} (heta : 0 < eta) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ (r : ℝ) (hr : 1 ≤ r), |r - 1| < delta →
      ∀ {d : ℕ} (p : Fin d → FlatCoreSpace R) (v : FlatCoreSpace R),
        ‖source hr C N p v‖ ≤ eta * ‖v‖ := by
  obtain ⟨delta, hdelta, hd⟩ :=
    RhNativeBilinearSmallness.uniform_actual_bilinear_smallness hR C N heta
  refine ⟨delta, hdelta, ?_⟩
  intro r hr hclose d p v
  exact source_norm_bound hr C N p heta.le (hd r hr hclose) v

end RhPerturbationSource
#print axioms RhPerturbationSource.source_weak
#print axioms RhPerturbationSource.source_is_outward_on_zero_row
#print axioms RhPerturbationSource.source_norm_bound
#print axioms RhPerturbationSource.local_actual_source_norm
