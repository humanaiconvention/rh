import RhPhysicalProjectionSchur001

/-! An isotropic subspace whose PHYSICAL projection is onto forces the actual
outward Schur residual to be nonpositive. Positivity would therefore require
exact equality. The existence/projection-surjectivity of a transported actual
old nullspace is NOT assumed proved here. -/
set_option maxHeartbeats 100000
set_option synthInstance.maxHeartbeats 20000
noncomputable section
open Set MeasureTheory
open scoped Topology BigOperators
namespace RhIsotropicSchurObstruction
open RhWeightedMeasureEmbedding RhFlatSmoothCore RhPhysicalOrthogonalSchur
open RhPulledCompleteForm RhFixedPhysicalPulledSchur RhFixedPhysicalSchurMatrix
open RhPhysicalProjectionSchur

def completionVector {d : ℕ} {R r : ℝ} (hr : 1 ≤ r)
    (C : ℝ) (N : ℕ) (p : Fin d → FlatCoreSpace R) {mu eta : ℝ}
    (h : Control hr C N p mu eta) (v : FlatCoreSpace R) (q : ComplementSpace R p) :
    ComplementSpace R p := q + RhFixedPhysicalPulledSchur.inverse hr C N p h
      (RhFixedPhysicalPulledSchur.crossSource hr C N p v)

theorem whole_form_completion_square {d : ℕ} {R r : ℝ} (hr : 1 ≤ r)
    (C : ℝ) (N : ℕ) (p : Fin d → FlatCoreSpace R) {mu eta : ℝ}
    (h : Control hr C N p mu eta) (v : FlatCoreSpace R) (q : ComplementSpace R p) :
    pulledForm hr C N (v + toCore R p q) (v + toCore R p q) =
      RhFixedPhysicalPulledSchur.residual hr C N p h v +
        pulledComplement hr C N p (completionVector hr C N p h v q)
          (completionVector hr C N p h v q) := by
  rw [RhFixedPhysicalPulledSchur.whole_form_expansion]
  exact RhCoerciveSchurInverse.completion_square
    (pulledComplement hr C N p) (pulled_isCoercive hr C N p h)
    (pulled_symmetric hr C N p) (pulledForm hr C N v v)
    (RhFixedPhysicalPulledSchur.crossSource hr C N p v) q
theorem residual_le_whole {d : ℕ} {R r : ℝ} (hr : 1 ≤ r)
    (C : ℝ) (N : ℕ) (p : Fin d → FlatCoreSpace R) {mu eta : ℝ}
    (h : Control hr C N p mu eta) (v : FlatCoreSpace R) (q : ComplementSpace R p) :
    RhFixedPhysicalPulledSchur.residual hr C N p h v ≤
      pulledForm hr C N (v + toCore R p q) (v + toCore R p q) := by
  let b := RhFixedPhysicalPulledSchur.crossSource hr C N p v
  let T := RhFixedPhysicalPulledSchur.inverse hr C N p h
  have hid : pulledForm hr C N (v + toCore R p q) (v + toCore R p q) =
      RhFixedPhysicalPulledSchur.residual hr C N p h v +
        pulledComplement hr C N p (q + T b) (q + T b) := by
    rw [RhFixedPhysicalPulledSchur.whole_form_expansion]
    exact RhCoerciveSchurInverse.completion_square
      (pulledComplement hr C N p) (pulled_isCoercive hr C N p h)
      (pulled_symmetric hr C N p) (pulledForm hr C N v v) b q
  obtain ⟨c, hc, hco⟩ := pulled_isCoercive hr C N p h
  have hnonneg : 0 ≤ pulledComplement hr C N p (q + T b) (q + T b) :=
    (by positivity : 0 ≤ c * ‖q + T b‖ * ‖q + T b‖).trans (hco (q + T b))
  linarith

/-- Exact finite-dimensional graph criterion. W may be any actual isotropic
subspace. Only its physical-coordinate surjectivity is needed, not a norm
identification or graph-orthogonal projection. -/
theorem isotropic_surjection_residual_nonpositive {d : ℕ} {R r : ℝ} (hr : 1 ≤ r)
    (C : ℝ) (N : ℕ) (p : Fin d → FlatCoreSpace R)
    (hp : Orthonormal ℝ (fun i => physicalEmbedding (p i : WeightedSpace)))
    {mu eta : ℝ} (h : Control hr C N p mu eta)
    (W : Submodule ℝ (FlatCoreSpace R))
    (hW : ∀ w : W, pulledForm hr C N (w : FlatCoreSpace R) (w : FlatCoreSpace R) = 0)
    (honto : Function.Surjective (fun w : W => coefficients p (w : FlatCoreSpace R))) :
    ∀ c : Fin d → ℝ, ∑ i, ∑ j, c i * c j * schurMatrix hr C N p h i j ≤ 0 := by
  intro c
  obtain ⟨w, hw⟩ := honto c
  have heq : combination p c + toCore R p (remainder p hp (w : FlatCoreSpace R)) =
      (w : FlatCoreSpace R) := by
    rw [← hw]
    exact physical_decomposition p hp (w : FlatCoreSpace R)
  have hbound := residual_le_whole hr C N p h (combination p c)
    (remainder p hp (w : FlatCoreSpace R))
  rw [heq, hW w, residual_combination] at hbound
  exact hbound

/-- If the whole outward form is positive, its finite residual must vanish
EXACTLY in the presence of such an isotropic graph. No residual sign is
inferred unconditionally. -/
theorem isotropic_surjection_forces_zero_of_positive {d : ℕ} {R r : ℝ} (hr : 1 ≤ r)
    (C : ℝ) (N : ℕ) (p : Fin d → FlatCoreSpace R)
    (hp : Orthonormal ℝ (fun i => physicalEmbedding (p i : WeightedSpace)))
    {mu eta : ℝ} (h : Control hr C N p mu eta)
    (W : Submodule ℝ (FlatCoreSpace R))
    (hW : ∀ w : W, pulledForm hr C N (w : FlatCoreSpace R) (w : FlatCoreSpace R) = 0)
    (honto : Function.Surjective (fun w : W => coefficients p (w : FlatCoreSpace R)))
    (hpositive : ∀ F : FlatCoreSpace R, 0 ≤ pulledForm hr C N F F) :
    ∀ c : Fin d → ℝ, ∑ i, ∑ j, c i * c j * schurMatrix hr C N p h i j = 0 := by
  intro c
  apply le_antisymm
  · exact isotropic_surjection_residual_nonpositive hr C N p hp h W hW honto c
  · exact (full_core_schur_iff hr C N p hp h).mp hpositive c

/-- The exact signed ledger at an isotropic vector, BEFORE any inequality. -/
theorem coordinate_isotropic_factorization {d : ℕ} {R r : ℝ} (hr : 1 ≤ r)
    (C : ℝ) (N : ℕ) (p : Fin d → FlatCoreSpace R)
    (hp : Orthonormal ℝ (fun i => physicalEmbedding (p i : WeightedSpace)))
    {mu eta : ℝ} (h : Control hr C N p mu eta) (w : FlatCoreSpace R)
    (c : Fin d → ℝ) (hw : coefficients p w = c)
    (hzero : pulledForm hr C N w w = 0) :
    (∑ i, ∑ j, c i * c j * schurMatrix hr C N p h i j) =
      -pulledComplement hr C N p
        (completionVector hr C N p h (combination p c) (remainder p hp w))
        (completionVector hr C N p h (combination p c) (remainder p hp w)) := by
  have heq : combination p c + toCore R p (remainder p hp w) = w := by
    rw [← hw]
    exact physical_decomposition p hp w
  have hid := whole_form_completion_square hr C N p h (combination p c) (remainder p hp w)
  rw [heq, hzero, residual_combination] at hid
  linarith

lemma complement_energy_eq_zero_iff {d : ℕ} {R r : ℝ} (hr : 1 ≤ r)
    (C : ℝ) (N : ℕ) (p : Fin d → FlatCoreSpace R) {mu eta : ℝ}
    (h : Control hr C N p mu eta) (z : ComplementSpace R p) :
    pulledComplement hr C N p z z = 0 ↔ z = 0 := by
  constructor
  · intro hz
    have hg := outward_graph_gap hr C N p h z
    have hc := sub_pos.mpr h.smaller
    have hn2 : ‖z‖ ^ 2 = 0 := by nlinarith [sq_nonneg ‖z‖]
    have hn : ‖z‖ = 0 := by nlinarith [norm_nonneg z]
    exact norm_eq_zero.mp hn
  · intro hz
    subst z
    simp

/-- Exact compensation is equivalent to vanishing of the ENTIRE completed
complement vector. It is not supplied by a first-derivative estimate. -/
theorem isotropic_residual_zero_iff_completed_vector_zero {d : ℕ} {R r : ℝ}
    (hr : 1 ≤ r) (C : ℝ) (N : ℕ) (p : Fin d → FlatCoreSpace R)
    (hp : Orthonormal ℝ (fun i => physicalEmbedding (p i : WeightedSpace)))
    {mu eta : ℝ} (h : Control hr C N p mu eta) (w : FlatCoreSpace R)
    (c : Fin d → ℝ) (hw : coefficients p w = c)
    (hzero : pulledForm hr C N w w = 0) :
    (∑ i, ∑ j, c i * c j * schurMatrix hr C N p h i j) = 0 ↔
      completionVector hr C N p h (combination p c) (remainder p hp w) = 0 := by
  rw [coordinate_isotropic_factorization hr C N p hp h w c hw hzero, neg_eq_zero]
  exact complement_energy_eq_zero_iff hr C N p h _
end RhIsotropicSchurObstruction
#print axioms RhIsotropicSchurObstruction.residual_le_whole
#print axioms RhIsotropicSchurObstruction.isotropic_surjection_residual_nonpositive
#print axioms RhIsotropicSchurObstruction.isotropic_surjection_forces_zero_of_positive
#print axioms RhIsotropicSchurObstruction.coordinate_isotropic_factorization
#print axioms RhIsotropicSchurObstruction.isotropic_residual_zero_iff_completed_vector_zero
