import RhFixedPhysicalSchurMatrix001

/-! Exact real polarization: vanishing of every Schur quadratic is literally
matrix zero, not a numerical tolerance or an approximate cancellation. -/
set_option maxHeartbeats 100000
noncomputable section
open scoped BigOperators
namespace RhSchurMatrixZero
open RhFlatSmoothCore RhFixedPhysicalPulledSchur RhFixedPhysicalSchurMatrix

theorem symmetric_matrix_zero_of_quadratics_zero {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ)
    (hsym : ∀ i j, M i j = M j i)
    (hzero : ∀ c : Fin d → ℝ, ∑ i, ∑ j, c i * c j * M i j = 0) : M = 0 := by
  classical
  have hd (i : Fin d) : M i i = 0 := by
    simpa [Pi.single_apply] using hzero (Pi.single i 1)
  ext i j
  have h := hzero (Pi.single i 1 + Pi.single j 1)
  simp only [Pi.add_apply, add_mul, mul_add, Finset.sum_add_distrib] at h
  simp [Pi.single_apply] at h
  rw [hd i, hd j, hsym j i] at h
  change M i j = 0
  linarith

theorem schurMatrix_zero_iff {d : ℕ} {R r : ℝ} (hr : 1 ≤ r)
    (C : ℝ) (N : ℕ) (p : Fin d → FlatCoreSpace R) {mu eta : ℝ}
    (h : Control hr C N p mu eta) :
    schurMatrix hr C N p h = 0 ↔
      ∀ c : Fin d → ℝ, ∑ i, ∑ j, c i * c j * schurMatrix hr C N p h i j = 0 := by
  constructor
  · intro hz c
    simp only [hz, Matrix.zero_apply, mul_zero, Finset.sum_const_zero]
  · intro hz
    exact symmetric_matrix_zero_of_quadratics_zero (schurMatrix hr C N p h)
      (schurMatrix_symmetric hr C N p h) hz

end RhSchurMatrixZero
#print axioms RhSchurMatrixZero.symmetric_matrix_zero_of_quadratics_zero
#print axioms RhSchurMatrixZero.schurMatrix_zero_iff