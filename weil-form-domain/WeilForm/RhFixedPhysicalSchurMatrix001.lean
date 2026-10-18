import RhFixedPhysicalPulledSchur001

/-! The literal finite-family matrix of the ACTUAL outward Schur residual.
The family is arbitrary; identifying its span with the physical nullspace
requires a separate theorem. No matrix nonnegativity is asserted. -/
set_option maxHeartbeats 100000
set_option synthInstance.maxHeartbeats 20000
noncomputable section
open Set MeasureTheory
open scoped Topology BigOperators
namespace RhFixedPhysicalSchurMatrix
open RhWeightedMeasureEmbedding RhFlatSmoothCore RhPhysicalOrthogonalSchur
open RhPulledCompleteForm RhFixedPhysicalPulledSchur

def combination {d : ℕ} {R : ℝ} (p : Fin d → FlatCoreSpace R)
    (c : Fin d → ℝ) : FlatCoreSpace R := ∑ i, c i • p i

def schurMatrix {d : ℕ} {R r : ℝ} (hr : 1 ≤ r) (C : ℝ) (N : ℕ)
    (p : Fin d → FlatCoreSpace R) {mu eta : ℝ} (h : Control hr C N p mu eta) :
    Matrix (Fin d) (Fin d) ℝ := fun i j =>
  pulledForm hr C N (p i) (p j) -
    inner ℝ (RhFixedPhysicalPulledSchur.crossSource hr C N p (p i))
      (RhFixedPhysicalPulledSchur.inverse hr C N p h
        (RhFixedPhysicalPulledSchur.crossSource hr C N p (p j)))

lemma inverse_pairing_symmetric {d : ℕ} {R r : ℝ} (hr : 1 ≤ r)
    (C : ℝ) (N : ℕ) (p : Fin d → FlatCoreSpace R) {mu eta : ℝ}
    (h : Control hr C N p mu eta) (b z : ComplementSpace R p) :
    inner ℝ b (RhFixedPhysicalPulledSchur.inverse hr C N p h z) =
      inner ℝ z (RhFixedPhysicalPulledSchur.inverse hr C N p h b) := by
  calc
    _ = pulledForm hr C N
        (toCore R p (RhFixedPhysicalPulledSchur.inverse hr C N p h b))
        (toCore R p (RhFixedPhysicalPulledSchur.inverse hr C N p h z)) :=
      (RhFixedPhysicalPulledSchur.inverse_weak_equation hr C N p h b _).symm
    _ = pulledForm hr C N
        (toCore R p (RhFixedPhysicalPulledSchur.inverse hr C N p h z))
        (toCore R p (RhFixedPhysicalPulledSchur.inverse hr C N p h b)) :=
      pulledForm_symmetric hr C N _ _
    _ = _ := RhFixedPhysicalPulledSchur.inverse_weak_equation hr C N p h z _

theorem schurMatrix_symmetric {d : ℕ} {R r : ℝ} (hr : 1 ≤ r)
    (C : ℝ) (N : ℕ) (p : Fin d → FlatCoreSpace R) {mu eta : ℝ}
    (h : Control hr C N p mu eta) (i j : Fin d) :
    schurMatrix hr C N p h i j = schurMatrix hr C N p h j i := by
  unfold schurMatrix
  rw [pulledForm_symmetric hr C N (p i) (p j),
    inverse_pairing_symmetric hr C N p h]

lemma source_combination {d : ℕ} {R r : ℝ} (hr : 1 ≤ r) (C : ℝ) (N : ℕ)
    (p : Fin d → FlatCoreSpace R) (c : Fin d → ℝ) :
    RhFixedPhysicalPulledSchur.crossSource hr C N p (combination p c) =
      ∑ i, c i • RhFixedPhysicalPulledSchur.crossSource hr C N p (p i) := by
  apply ext_inner_right ℝ
  intro q
  rw [RhFixedPhysicalPulledSchur.crossSource_weak, sum_inner]
  simp only [combination, map_sum, map_smul, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [real_inner_smul_left (RhFixedPhysicalPulledSchur.crossSource hr C N p (p i)) q (c i),
    RhFixedPhysicalPulledSchur.crossSource_weak]

lemma form_combination {d : ℕ} {R r : ℝ} (hr : 1 ≤ r) (C : ℝ) (N : ℕ)
    (p : Fin d → FlatCoreSpace R) (c : Fin d → ℝ) :
    pulledForm hr C N (combination p c) (combination p c) =
      ∑ i, ∑ j, c i * c j * pulledForm hr C N (p i) (p j) := by
  simp only [combination, map_sum, map_smul, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

lemma payment_combination {d : ℕ} {R r : ℝ} (hr : 1 ≤ r) (C : ℝ) (N : ℕ)
    (p : Fin d → FlatCoreSpace R) {mu eta : ℝ} (h : Control hr C N p mu eta)
    (c : Fin d → ℝ) :
    inner ℝ (RhFixedPhysicalPulledSchur.crossSource hr C N p (combination p c))
      (RhFixedPhysicalPulledSchur.inverse hr C N p h
        (RhFixedPhysicalPulledSchur.crossSource hr C N p (combination p c))) =
      ∑ i, ∑ j, c i * c j *
        inner ℝ (RhFixedPhysicalPulledSchur.crossSource hr C N p (p i))
          (RhFixedPhysicalPulledSchur.inverse hr C N p h
            (RhFixedPhysicalPulledSchur.crossSource hr C N p (p j))) := by
  rw [source_combination]
  simp only [map_sum, map_smul, sum_inner, inner_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [real_inner_smul_left (RhFixedPhysicalPulledSchur.crossSource hr C N p (p i))
    (c j • RhFixedPhysicalPulledSchur.inverse hr C N p h
      (RhFixedPhysicalPulledSchur.crossSource hr C N p (p j))) (c i),
    real_inner_smul_right (RhFixedPhysicalPulledSchur.crossSource hr C N p (p i))
      (RhFixedPhysicalPulledSchur.inverse hr C N p h
        (RhFixedPhysicalPulledSchur.crossSource hr C N p (p j))) (c j)]
  ring

theorem residual_combination {d : ℕ} {R r : ℝ} (hr : 1 ≤ r)
    (C : ℝ) (N : ℕ) (p : Fin d → FlatCoreSpace R) {mu eta : ℝ}
    (h : Control hr C N p mu eta) (c : Fin d → ℝ) :
    RhFixedPhysicalPulledSchur.residual hr C N p h (combination p c) =
      ∑ i, ∑ j, c i * c j * schurMatrix hr C N p h i j := by
  unfold RhFixedPhysicalPulledSchur.residual
  rw [form_combination, payment_combination]
  simp only [schurMatrix, mul_sub, Finset.sum_sub_distrib]

/-- Exact coordinate formulation; no sign, nullness, independence or spanning
of this family is assumed to prove the identity. -/
theorem family_schur_iff {d : ℕ} {R r : ℝ} (hr : 1 ≤ r)
    (C : ℝ) (N : ℕ) (p : Fin d → FlatCoreSpace R) {mu eta : ℝ}
    (h : Control hr C N p mu eta) :
    (∀ (c : Fin d → ℝ) (q : ComplementSpace R p),
      0 ≤ pulledForm hr C N (combination p c + toCore R p q)
        (combination p c + toCore R p q)) ↔
      ∀ c : Fin d → ℝ, 0 ≤ ∑ i, ∑ j, c i * c j * schurMatrix hr C N p h i j := by
  constructor
  · intro hall c
    have hs := (RhFixedPhysicalPulledSchur.actual_schur_iff hr C N p h
      (combination p c)).mp (hall c)
    simpa only [residual_combination] using hs
  · intro hall c
    apply (RhFixedPhysicalPulledSchur.actual_schur_iff hr C N p h
      (combination p c)).mpr
    simpa only [residual_combination] using hall c

end RhFixedPhysicalSchurMatrix
#print axioms RhFixedPhysicalSchurMatrix.schurMatrix_symmetric
#print axioms RhFixedPhysicalSchurMatrix.residual_combination
#print axioms RhFixedPhysicalSchurMatrix.family_schur_iff