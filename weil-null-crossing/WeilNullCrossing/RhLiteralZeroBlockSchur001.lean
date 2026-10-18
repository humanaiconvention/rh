import RhPhysicalProjectionSchur001
import RhSchurMatrixZero001

/-! Literal isotropic low block and the FULL outward cross-source.
The actual complement Control and exact whole-zero low block are explicit
premises. No source is replaced by its perturbation part. No native zero
block, inverse gap, or residual nonzero assertion is supplied here.
-/
set_option maxHeartbeats 100000
set_option synthInstance.maxHeartbeats 20000
noncomputable section
open Set MeasureTheory
open scoped Topology BigOperators
namespace RhLiteralZeroBlockSchur
open RhWeightedMeasureEmbedding RhFlatSmoothCore RhPhysicalOrthogonalSchur
open RhPulledCompleteForm RhFixedPhysicalPulledSchur RhFixedPhysicalSchurMatrix

/-- Strict complement coercivity makes zero inverse payment equivalent to a
zero complete source. This uses the actual constructed common inverse. -/
theorem payment_zero_iff {d : ℕ} {R r : ℝ} (hr : 1 ≤ r) (C : ℝ) (N : ℕ)
    (w : Fin d → FlatCoreSpace R) {mu eta : ℝ} (h : Control hr C N w mu eta)
    (b : ComplementSpace R w) :
    inner ℝ b (RhFixedPhysicalPulledSchur.inverse hr C N w h b) = 0 ↔ b = 0 := by
  constructor
  · intro hpay
    let z := RhFixedPhysicalPulledSchur.inverse hr C N w h b
    have hc : 0 < mu / (mu + RhCompleteFormBound.boundConstant R C N + 1) - eta :=
      sub_pos.mpr h.smaller
    have hpayz : inner ℝ b z = 0 := hpay
    have hg := outward_graph_gap hr C N w h z
    rw [pulledComplement_apply, RhFixedPhysicalPulledSchur.inverse_weak_equation, hpayz] at hg
    change (mu / (mu + RhCompleteFormBound.boundConstant R C N + 1) - eta) *
      ‖z‖ ^ 2 ≤ 0 at hg
    have hz2 : ‖z‖ ^ 2 = 0 := by nlinarith [sq_nonneg ‖z‖]
    have hz : z = 0 := norm_eq_zero.mp (sq_eq_zero_iff.mp hz2)
    have hb := RhFixedPhysicalPulledSchur.inverse_weak_equation hr C N w h b b
    change pulledForm hr C N (toCore R w z) (toCore R w b) = inner ℝ b b at hb
    rw [hz] at hb
    simp only [map_zero, ContinuousLinearMap.zero_apply] at hb
    have hb2 : ‖b‖ ^ 2 = 0 := by rw [← real_inner_self_eq_norm_sq]; exact hb.symm
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp hb2)
  · intro hb
    simp only [hb, map_zero, inner_zero_left]

/-- Every signed covariance entry uses ONE inverse of the complete complement. -/
theorem schur_entry {d : ℕ} {R r : ℝ} (hr : 1 ≤ r) (C : ℝ) (N : ℕ)
    (w : Fin d → FlatCoreSpace R) {mu eta : ℝ} (h : Control hr C N w mu eta)
    (hzero : ∀ i j, pulledForm hr C N (w i) (w j) = 0) (i j : Fin d) :
    schurMatrix hr C N w h i j =
      - inner ℝ (RhFixedPhysicalPulledSchur.crossSource hr C N w (w i))
        (RhFixedPhysicalPulledSchur.inverse hr C N w h
          (RhFixedPhysicalPulledSchur.crossSource hr C N w (w j))) := by
  simp only [schurMatrix, hzero i j, zero_sub]

/-- Exact negative semidefiniteness of the Schur matrix from a zero low block. -/
theorem schur_quadratic_nonpositive {d : ℕ} {R r : ℝ} (hr : 1 ≤ r)
    (C : ℝ) (N : ℕ) (w : Fin d → FlatCoreSpace R) {mu eta : ℝ}
    (h : Control hr C N w mu eta)
    (hzero : ∀ i j, pulledForm hr C N (w i) (w j) = 0) (c : Fin d → ℝ) :
    ∑ i, ∑ j, c i * c j * schurMatrix hr C N w h i j ≤ 0 := by
  have hf : pulledForm hr C N (combination w c) (combination w c) = 0 := by
    rw [form_combination]
    simp only [hzero, mul_zero, Finset.sum_const_zero]
  have he := residual_combination hr C N w h c
  unfold RhFixedPhysicalPulledSchur.residual at he
  rw [hf, zero_sub] at he
  rw [← he]
  exact neg_nonpos.mpr (payment_nonnegative hr C N w h (combination w c))

/-- Zero means exact full cross-source annihilation, not an error tolerance. -/
theorem matrix_zero_iff_full_sources_zero {d : ℕ} {R r : ℝ} (hr : 1 ≤ r)
    (C : ℝ) (N : ℕ) (w : Fin d → FlatCoreSpace R) {mu eta : ℝ}
    (h : Control hr C N w mu eta)
    (hzero : ∀ i j, pulledForm hr C N (w i) (w j) = 0) :
    schurMatrix hr C N w h = 0 ↔
      ∀ i, RhFixedPhysicalPulledSchur.crossSource hr C N w (w i) = 0 := by
  constructor
  · intro hmatrix i
    have hd := congrFun (congrFun hmatrix i) i
    rw [schur_entry hr C N w h hzero] at hd
    change - inner ℝ (RhFixedPhysicalPulledSchur.crossSource hr C N w (w i))
      (RhFixedPhysicalPulledSchur.inverse hr C N w h
        (RhFixedPhysicalPulledSchur.crossSource hr C N w (w i))) = 0 at hd
    apply (payment_zero_iff hr C N w h _).mp
    linarith
  · intro hs
    ext i j
    simp only [schur_entry hr C N w h hzero, hs i, inner_zero_left, neg_zero,
      Matrix.zero_apply]

/-- Full-core positivity iff every FULL row-to-complement cross-source is
zero. The physical projector semantics are justified by the ON premise. -/
theorem full_core_nonnegative_iff_full_sources_zero {d : ℕ} {R r : ℝ}
    (hr : 1 ≤ r) (C : ℝ) (N : ℕ) (w : Fin d → FlatCoreSpace R)
    (hw : Orthonormal ℝ (fun i => physicalEmbedding (w i : WeightedSpace)))
    {mu eta : ℝ} (h : Control hr C N w mu eta)
    (hzero : ∀ i j, pulledForm hr C N (w i) (w j) = 0) :
    (∀ F : FlatCoreSpace R, 0 ≤ pulledForm hr C N F F) ↔
      ∀ i, RhFixedPhysicalPulledSchur.crossSource hr C N w (w i) = 0 := by
  rw [← matrix_zero_iff_full_sources_zero hr C N w h hzero]
  constructor
  · intro hpos
    apply (RhSchurMatrixZero.schurMatrix_zero_iff hr C N w h).mpr
    intro c
    exact le_antisymm (schur_quadratic_nonpositive hr C N w h hzero c)
      ((RhPhysicalProjectionSchur.full_core_schur_iff hr C N w hw h).mp hpos c)
  · intro hz
    apply (RhPhysicalProjectionSchur.full_core_schur_iff hr C N w hw h).mpr
    intro c
    simp only [hz, Matrix.zero_apply, mul_zero, Finset.sum_const_zero, le_refl]

end RhLiteralZeroBlockSchur
#print axioms RhLiteralZeroBlockSchur.payment_zero_iff
#print axioms RhLiteralZeroBlockSchur.schur_entry
#print axioms RhLiteralZeroBlockSchur.schur_quadratic_nonpositive
#print axioms RhLiteralZeroBlockSchur.matrix_zero_iff_full_sources_zero
#print axioms RhLiteralZeroBlockSchur.full_core_nonnegative_iff_full_sources_zero
