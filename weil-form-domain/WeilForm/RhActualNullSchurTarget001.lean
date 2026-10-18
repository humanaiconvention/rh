import RhOldNullCoordinateSurjectivity001
import RhIsotropicSchurObstruction001
import RhFixedPhysicalLocalInverse001

/-! Actual old-null Schur target. Isotropy and local projection surjectivity
come from the CONSTRUCTED inward image of the TRUE base form kernel.
Complement inversion is genuinely constructed from the explicit base gap and
proved native dilation continuity. No residual nonzero/sign assumption is
inserted and no outward positivity is concluded. -/
set_option maxHeartbeats 100000
set_option synthInstance.maxHeartbeats 20000
noncomputable section
open Set MeasureTheory Filter
open scoped Topology BigOperators
namespace RhActualNullSchurTarget
open RhWeightedMeasureEmbedding RhFlatSmoothCore RhPhysicalOrthogonalSchur
open RhPulledCompleteForm RhFixedPhysicalPulledSchur RhFixedPhysicalSchurMatrix
open RhPhysicalProjectionSchur RhInwardOldNullLift RhInwardOldNullSubspace
open RhIsotropicSchurObstruction RhOldNullCoordinateSurjectivity

theorem actual_null_schur_nonpositive {d : ℕ} {R r : ℝ} (hR : 0 < R) (hr : 1 ≤ r)
    (C : ℝ) (N : ℕ) (p : Fin d → FlatCoreSpace R)
    (hp : Orthonormal ℝ (fun i => physicalEmbedding (p i : WeightedSpace)))
    {mu eta : ℝ} (h : Control hr C N p mu eta)
    (honto : Function.Surjective (fun w : outwardOldNullSpace hR hr C N =>
      coefficients p (w : FlatCoreSpace R))) :
    ∀ c : Fin d → ℝ, ∑ i, ∑ j, c i * c j * schurMatrix hr C N p h i j ≤ 0 :=
  isotropic_surjection_residual_nonpositive hr C N p hp h
    (outwardOldNullSpace hR hr C N) (outwardOldNullSpace_diagonal_zero hR hr C N) honto

/-- The remaining condition is EXACT whole completed-vector annihilation,
with the one actual complement inverse. It is not merely a small error. -/
theorem positivity_iff_exact_compensation {d : ℕ} {R r : ℝ} (hR : 0 < R) (hr : 1 ≤ r)
    (C : ℝ) (N : ℕ) (p : Fin d → FlatCoreSpace R)
    (hp : Orthonormal ℝ (fun i => physicalEmbedding (p i : WeightedSpace)))
    {mu eta : ℝ} (h : Control hr C N p mu eta)
    (honto : Function.Surjective (fun w : outwardOldNullSpace hR hr C N =>
      coefficients p (w : FlatCoreSpace R))) :
    (∀ F : FlatCoreSpace R, 0 ≤ pulledForm hr C N F F) ↔
      ∀ w : outwardOldNullSpace hR hr C N,
        completionVector hr C N p h
          (combination p (coefficients p (w : FlatCoreSpace R)))
          (remainder p hp (w : FlatCoreSpace R)) = 0 := by
  constructor
  · intro hpositive w
    apply (isotropic_residual_zero_iff_completed_vector_zero hr C N p hp h
      (w : FlatCoreSpace R) (coefficients p (w : FlatCoreSpace R)) rfl
      (outwardOldNullSpace_diagonal_zero hR hr C N w)).mp
    apply le_antisymm
    · exact actual_null_schur_nonpositive hR hr C N p hp h honto _
    · exact (full_core_schur_iff hr C N p hp h).mp hpositive _
  · intro hcompensate
    apply (full_core_schur_iff hr C N p hp h).mpr
    intro c
    obtain ⟨w, hw⟩ := honto c
    have hzero := (isotropic_residual_zero_iff_completed_vector_zero hr C N p hp h
      (w : FlatCoreSpace R) (coefficients p (w : FlatCoreSpace R)) rfl
      (outwardOldNullSpace_diagonal_zero hR hr C N w)).mpr (hcompensate w)
    change coefficients p (w : FlatCoreSpace R) = c at hw
    rw [hw] at hzero
    exact hzero.ge

/-- All locality, projection surjectivity, and inverse requirements are PROVED
here from actual null membership and a base PHYSICAL gap. The output is a
precise equivalent target; no equality in that target is asserted. -/
theorem exists_local_actual_null_schur_target {d : ℕ} {R : ℝ} (hR : 0 < R)
    (C : ℝ) (N : ℕ) (p : Fin d → FlatCoreSpace R)
    (hp : Orthonormal ℝ (fun i => physicalEmbedding (p i : WeightedSpace)))
    (hn : ∀ i, p i ∈ baseNullSpace R C N) {mu : ℝ}
    (hmu : 0 < mu) (hgap : PhysicalGap R C N p mu) :
    ∃ delta > 0, ∀ (r : ℝ) (hr : 1 ≤ r), |r - 1| < delta →
      ∃ h : Control hr C N p mu
        ((mu / (mu + RhCompleteFormBound.boundConstant R C N + 1)) / 2),
        (∀ c : Fin d → ℝ, ∑ i, ∑ j, c i * c j * schurMatrix hr C N p h i j ≤ 0) ∧
          ((∀ F : FlatCoreSpace R, 0 ≤ pulledForm hr C N F F) ↔
            ∀ c : Fin d → ℝ, ∑ i, ∑ j, c i * c j * schurMatrix hr C N p h i j = 0) := by
  obtain ⟨da, hda, hcontrol⟩ :=
    RhFixedPhysicalLocalInverse.exists_local_control hR C N p hmu hgap
  obtain ⟨db, hdb, hprojection⟩ :=
    exists_local_physical_coordinates_surjective hR C N p hp hn
  let delta := min 1 (min da db)
  have hdelta : 0 < delta := lt_min (by norm_num) (lt_min hda hdb)
  refine ⟨delta, hdelta, ?_⟩
  intro r hr hclose
  have hnear1 : |r - 1| < 1 := hclose.trans_le (min_le_left _ _)
  have hr2 : r ≤ 2 := by
    rw [abs_of_nonneg (sub_nonneg.mpr hr)] at hnear1
    linarith
  have hca : |r - 1| < da :=
    hclose.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hcb : |r - 1| < db :=
    hclose.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  let hc := hcontrol r hr hca
  have honto := hprojection (⟨r, hr, hr2⟩ : Scale) hcb
  have hnonpos := actual_null_schur_nonpositive hR hr C N p hp hc honto
  refine ⟨hc, hnonpos, ?_⟩
  constructor
  · intro hpositive c
    exact le_antisymm (hnonpos c) ((full_core_schur_iff hr C N p hp hc).mp hpositive c)
  · intro hzero
    apply (full_core_schur_iff hr C N p hp hc).mpr
    intro c
    exact (hzero c).ge

end RhActualNullSchurTarget
#print axioms RhActualNullSchurTarget.actual_null_schur_nonpositive
#print axioms RhActualNullSchurTarget.positivity_iff_exact_compensation
#print axioms RhActualNullSchurTarget.exists_local_actual_null_schur_target