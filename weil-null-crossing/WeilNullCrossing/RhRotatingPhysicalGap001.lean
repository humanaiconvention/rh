import RhPhysicalProjectionSchur001

/-! Exact finite rotation of the PHYSICAL orthogonal complement. Only the
old family is orthonormal and null. The moving family is not silently assumed
to lie in the old radical. No residual sign or global margin is proved. -/
noncomputable section
set_option maxHeartbeats 150000
set_option synthInstance.maxHeartbeats 20000
open Set MeasureTheory
open scoped Topology BigOperators
namespace RhRotatingPhysicalGap
open RhWeightedMeasureEmbedding RhFlatSmoothCore RhNativeCompleteBilinear
open RhPhysicalOrthogonalSchur RhPhysicalProjectionSchur RhPulledCompleteForm
open RhFixedPhysicalPulledSchur RhFixedPhysicalSchurMatrix

def rotationError {d : ℕ} {R : ℝ} (p w : Fin d → FlatCoreSpace R) : ℝ :=
  ∑ i, ‖physicalEmbedding (p i : WeightedSpace) - physicalEmbedding (w i : WeightedSpace)‖^2

lemma projection_norm_square {d : ℕ} {R : ℝ} (p : Fin d → FlatCoreSpace R)
    (hp : Orthonormal ℝ (fun i => physicalEmbedding (p i : WeightedSpace)))
    (z : FlatCoreSpace R) :
    ‖physicalEmbedding (projection p z : WeightedSpace)‖^2 =
      ∑ i, (coefficients p z i)^2 := by
  change ‖physicalEmbedding (combination p (coefficients p z) : WeightedSpace)‖^2 = _
  rw [physical_combination, ← real_inner_self_eq_norm_sq, sum_inner]
  simp_rw [real_inner_smul_left, hp.inner_right_fintype]
  simp only [pow_two]

lemma projection_inner {d : ℕ} {R : ℝ} (p : Fin d → FlatCoreSpace R)
    (hp : Orthonormal ℝ (fun i => physicalEmbedding (p i : WeightedSpace)))
    (z : FlatCoreSpace R) :
    inner ℝ (physicalEmbedding (projection p z : WeightedSpace))
      (physicalEmbedding (z : WeightedSpace)) =
      ‖physicalEmbedding (projection p z : WeightedSpace)‖^2 := by
  rw [projection_norm_square p hp z]
  change inner ℝ (physicalEmbedding (combination p (coefficients p z) : WeightedSpace)) _ = _
  rw [physical_combination, sum_inner]
  simp only [real_inner_smul_left, coefficients, pow_two]

lemma remainder_mass {d : ℕ} {R : ℝ} (p : Fin d → FlatCoreSpace R)
    (hp : Orthonormal ℝ (fun i => physicalEmbedding (p i : WeightedSpace)))
    (z : FlatCoreSpace R) :
    ‖physicalEmbedding (remainder p hp z : WeightedSpace)‖^2 =
      ‖physicalEmbedding (z : WeightedSpace)‖^2 -
      ‖physicalEmbedding (projection p z : WeightedSpace)‖^2 := by
  change ‖physicalEmbedding ((z : WeightedSpace) - (projection p z : WeightedSpace))‖^2 = _
  rw [map_sub, norm_sub_sq_real, real_inner_comm,
    projection_inner p hp z]
  ring

/-- Exact physical projection cost against an arbitrary finite moving family. -/
theorem projection_rotation_bound {d : ℕ} {R : ℝ}
    (p w : Fin d → FlatCoreSpace R)
    (hp : Orthonormal ℝ (fun i => physicalEmbedding (p i : WeightedSpace)))
    (z : FlatCoreSpace R)
    (hwz : ∀ i, inner ℝ (physicalEmbedding (w i : WeightedSpace))
      (physicalEmbedding (z : WeightedSpace)) = 0) :
    ‖physicalEmbedding (projection p z : WeightedSpace)‖^2 ≤
      rotationError p w * ‖physicalEmbedding (z : WeightedSpace)‖^2 := by
  rw [projection_norm_square p hp z, rotationError, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i hi
  have he : coefficients p z i = inner ℝ
      (physicalEmbedding (p i : WeightedSpace) - physicalEmbedding (w i : WeightedSpace))
      (physicalEmbedding (z : WeightedSpace)) := by
    simp only [inner_sub_left, hwz i, sub_zero, coefficients]
  have hc := real_inner_mul_inner_self_le
    (physicalEmbedding (p i : WeightedSpace) - physicalEmbedding (w i : WeightedSpace))
    (physicalEmbedding (z : WeightedSpace))
  simpa only [he, pow_two, real_inner_self_eq_norm_sq] using hc

lemma projection_mem_kernel {d : ℕ} {R : ℝ} (C : ℝ) (N : ℕ)
    (p : Fin d → FlatCoreSpace R)
    (hn : ∀ i, p i ∈ (baseForm R C N).ker) (z : FlatCoreSpace R) :
    projection p z ∈ (baseForm R C N).ker := by
  unfold projection combination
  exact Submodule.sum_mem _ (fun i hi => Submodule.smul_mem _ _ (hn i))

lemma remainder_form {d : ℕ} {R : ℝ} (C : ℝ) (N : ℕ)
    (p : Fin d → FlatCoreSpace R)
    (hp : Orthonormal ℝ (fun i => physicalEmbedding (p i : WeightedSpace)))
    (hn : ∀ i, p i ∈ (baseForm R C N).ker) (z : FlatCoreSpace R) :
    completeForm R C N (remainder p hp z : WeightedSpace) (remainder p hp z : WeightedSpace) =
      completeForm R C N (z : WeightedSpace) (z : WeightedSpace) := by
  have hzero (y : FlatCoreSpace R) :
      completeForm R C N (projection p z : WeightedSpace) (y : WeightedSpace) = 0 := by
    have hk : baseForm R C N (projection p z) = 0 := projection_mem_kernel C N p hn z
    simpa only [baseForm_apply, ContinuousLinearMap.zero_apply] using
      congrArg (fun L : FlatCoreSpace R →L[ℝ] ℝ => L y) hk
  have hzP : completeForm R C N (z : WeightedSpace) (projection p z : WeightedSpace) = 0 := by
    rw [completeForm_symmetric]
    exact hzero z
  change completeForm R C N ((z : WeightedSpace) - (projection p z : WeightedSpace))
    ((z : WeightedSpace) - (projection p z : WeightedSpace)) = _
  simp only [map_sub, ContinuousLinearMap.sub_apply]
  rw [hzero z, hzero (projection p z), hzP]
  ring

/-- The old physical gap survives finite rotation with an exact factor 1/2.
All old radical cross pairings vanish as WHOLE native rows. -/
theorem rotated_physical_gap {d : ℕ} {R : ℝ} (C : ℝ) (N : ℕ)
    (p w : Fin d → FlatCoreSpace R)
    (hp : Orthonormal ℝ (fun i => physicalEmbedding (p i : WeightedSpace)))
    (hn : ∀ i, p i ∈ (baseForm R C N).ker) {mu : ℝ}
    (hmu : 0 < mu) (hgap : PhysicalGap R C N p mu)
    (hE : rotationError p w ≤ 1/2) : PhysicalGap R C N w (mu/2) := by
  intro q
  let z : FlatCoreSpace R := toCore R w q
  have hzorth : ∀ i, inner ℝ (physicalEmbedding (w i : WeightedSpace))
      (physicalEmbedding (z : WeightedSpace)) = 0 :=
    ((mem_complement_iff R w (q : WeightedSpace)).mp q.property).2
  have hproj := projection_rotation_bound p w hp z hzorth
  have hprojhalf : ‖physicalEmbedding (projection p z : WeightedSpace)‖^2 ≤
      (1/2) * ‖physicalEmbedding (z : WeightedSpace)‖^2 :=
    hproj.trans (mul_le_mul_of_nonneg_right hE (sq_nonneg _))
  have hrem : (1/2) * ‖physicalEmbedding (z : WeightedSpace)‖^2 ≤
      ‖physicalEmbedding (remainder p hp z : WeightedSpace)‖^2 := by
    rw [remainder_mass p hp z]
    linarith
  have hb := hgap (remainder p hp z)
  rw [remainder_form C N p hp hn z] at hb
  change (mu/2) * ‖physicalEmbedding (z : WeightedSpace)‖^2 ≤
    completeForm R C N (z : WeightedSpace) (z : WeightedSpace)
  calc
    _ = mu * ((1/2) * ‖physicalEmbedding (z : WeightedSpace)‖^2) := by ring
    _ ≤ mu * ‖physicalEmbedding (remainder p hp z : WeightedSpace)‖^2 :=
      mul_le_mul_of_nonneg_left hrem hmu.le
    _ ≤ _ := hb

/-- Existing complement inversion accepts this moving-family gap. The actual
perturbation budget remains explicit here; no smallness or sign is postulated. -/
def rotatedControl {d : ℕ} {R r : ℝ} (hr : 1 ≤ r) (C : ℝ) (N : ℕ)
    (p w : Fin d → FlatCoreSpace R)
    (hp : Orthonormal ℝ (fun i => physicalEmbedding (p i : WeightedSpace)))
    (hn : ∀ i, p i ∈ (baseForm R C N).ker) {mu eta : ℝ}
    (hmu : 0 < mu) (hgap : PhysicalGap R C N p mu)
    (hE : rotationError p w ≤ 1/2)
    (hpert : ∀ q : ComplementSpace R w,
      |differenceForm hr C N (toCore R w q) (toCore R w q)| ≤ eta * ‖q‖^2)
    (heta : eta < (mu/2) / (mu/2 + RhCompleteFormBound.boundConstant R C N + 1)) :
    Control hr C N w (mu/2) eta where
  positive_mu := half_pos hmu
  base_gap := rotated_physical_gap C N p w hp hn hmu hgap hE
  perturbation := hpert
  smaller := heta

end RhRotatingPhysicalGap
#print axioms RhRotatingPhysicalGap.projection_rotation_bound
#print axioms RhRotatingPhysicalGap.remainder_form
#print axioms RhRotatingPhysicalGap.rotated_physical_gap
#print axioms RhRotatingPhysicalGap.rotatedControl
