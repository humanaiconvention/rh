import RhIsotropicSchurObstruction001
import RhSchurMatrixZero001
import RhSmoothPhysicalTransfer001

/-! Conditional exact negative-witness transfer. This module does NOT prove
that a native Schur entry or matrix is nonzero. All forms use ONE fixed finite
horizon. The physical kernel dictionary requires C=archConstant explicitly. -/
set_option maxHeartbeats 100000
set_option synthInstance.maxHeartbeats 20000
noncomputable section
open Set MeasureTheory
open scoped Topology BigOperators ContDiff
namespace RhSchurNegativeWitness
open RhAnchored RhWeightedMeasureEmbedding RhNativeCompleteBilinear RhFlatSmoothCore
open RhPhysicalOrthogonalSchur RhPulledCompleteForm RhFixedPhysicalPulledSchur
open RhFixedPhysicalSchurMatrix RhIsotropicSchurObstruction RhSchurMatrixZero

def minimizingVector {d : ℕ} {R r : ℝ} (hr : 1 ≤ r) (C : ℝ) (N : ℕ)
    (p : Fin d → FlatCoreSpace R) {mu eta : ℝ} (h : Control hr C N p mu eta)
    (c : Fin d → ℝ) : FlatCoreSpace R :=
  combination p c + toCore R p
    (-(RhFixedPhysicalPulledSchur.inverse hr C N p h
      (RhFixedPhysicalPulledSchur.crossSource hr C N p (combination p c))))

/-- Exact minimizing vector and its energy, with no numerical minimization. -/
theorem minimizing_energy {d : ℕ} {R r : ℝ} (hr : 1 ≤ r) (C : ℝ) (N : ℕ)
    (p : Fin d → FlatCoreSpace R) {mu eta : ℝ} (h : Control hr C N p mu eta)
    (c : Fin d → ℝ) :
    pulledForm hr C N (minimizingVector hr C N p h c) (minimizingVector hr C N p h c) =
      ∑ i, ∑ j, c i * c j * schurMatrix hr C N p h i j := by
  let v := combination p c
  let q := -(RhFixedPhysicalPulledSchur.inverse hr C N p h
    (RhFixedPhysicalPulledSchur.crossSource hr C N p v))
  have hz : completionVector hr C N p h v q = 0 := by
    change -RhFixedPhysicalPulledSchur.inverse hr C N p h
      (RhFixedPhysicalPulledSchur.crossSource hr C N p v) +
        RhFixedPhysicalPulledSchur.inverse hr C N p h
          (RhFixedPhysicalPulledSchur.crossSource hr C N p v) = 0
    exact neg_add_cancel _
  have he := whole_form_completion_square hr C N p h v q
  rw [hz] at he
  simp only [map_zero, ContinuousLinearMap.zero_apply, add_zero] at he
  change pulledForm hr C N (v + toCore R p q) (v + toCore R p q) = _
  rw [he]
  exact residual_combination hr C N p h c

theorem nonzero_nonpositive_schur_has_negative_quadratic {d : ℕ} {R r : ℝ}
    (hr : 1 ≤ r) (C : ℝ) (N : ℕ) (p : Fin d → FlatCoreSpace R)
    {mu eta : ℝ} (h : Control hr C N p mu eta)
    (hnonpos : ∀ c : Fin d → ℝ,
      ∑ i, ∑ j, c i * c j * schurMatrix hr C N p h i j ≤ 0)
    (hne : schurMatrix hr C N p h ≠ 0) :
    ∃ c : Fin d → ℝ, ∑ i, ∑ j, c i * c j * schurMatrix hr C N p h i j < 0 := by
  by_contra hn
  push_neg at hn
  apply hne
  apply (schurMatrix_zero_iff hr C N p h).mpr
  intro c
  exact le_antisymm (hnonpos c) (hn c)

theorem nonzero_nonpositive_schur_negative_core {d : ℕ} {R r : ℝ}
    (hr : 1 ≤ r) (C : ℝ) (N : ℕ) (p : Fin d → FlatCoreSpace R)
    {mu eta : ℝ} (h : Control hr C N p mu eta)
    (hnonpos : ∀ c : Fin d → ℝ,
      ∑ i, ∑ j, c i * c j * schurMatrix hr C N p h i j ≤ 0)
    (hne : schurMatrix hr C N p h ≠ 0) :
    ∃ F : FlatCoreSpace R, pulledForm hr C N F F < 0 := by
  obtain ⟨c, hc⟩ := nonzero_nonpositive_schur_has_negative_quadratic hr C N p h hnonpos hne
  refine ⟨minimizingVector hr C N p h c, ?_⟩
  rwa [minimizing_energy]

/-- Native smooth physical negative witness ONLY under an explicit nonzero
Schur hypothesis. No all-prime interpretation beyond the finite horizon N. -/
theorem nonzero_nonpositive_schur_negative_smooth {d : ℕ} {R r : ℝ}
    (hR : 0 < R) (hr : 1 ≤ r) (N : ℕ) (p : Fin d → FlatCoreSpace R)
    {mu eta : ℝ} (h : Control hr archConstant N p mu eta)
    (hnonpos : ∀ c : Fin d → ℝ,
      ∑ i, ∑ j, c i * c j * schurMatrix hr archConstant N p h i j ≤ 0)
    (hne : schurMatrix hr archConstant N p h ≠ 0) :
    ∃ f : ℝ → ℝ, ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧
      tsupport f ⊆ Ioo (-(r * R)) (r * R) ∧
      kernelQuadratic (r * R) (RhAllPrime.completeKernel N) (deriv f) < 0 := by
  obtain ⟨F, hF⟩ := nonzero_nonpositive_schur_negative_core hr archConstant N p h hnonpos hne
  have hlarge : 0 < r * R := mul_pos (by linarith : 0 < r) hR
  apply RhSmoothPhysicalTransfer.negative_form_has_smooth_derivative hlarge N
    (RhFlatCoreDilation.outwardMap hr F)
  rw [← pulledForm_apply]
  exact hF

end RhSchurNegativeWitness
#print axioms RhSchurNegativeWitness.minimizing_energy
#print axioms RhSchurNegativeWitness.nonzero_nonpositive_schur_negative_core
#print axioms RhSchurNegativeWitness.nonzero_nonpositive_schur_negative_smooth