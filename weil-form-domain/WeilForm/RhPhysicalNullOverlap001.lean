import RhPhysicalOverlapFinite001
import RhInwardOldNullLift001

/-! Actual finite physical overlap of the inward old-support lifts.
The convergence premise is discharged by the actual weighted inward-dilation
limit. No nullspace, gap, or positivity premise is needed for this geometric
invertibility leg; isotropy is a separate native form identity.
-/
set_option maxHeartbeats 0
noncomputable section
open Set Filter
open scoped Topology BigOperators
namespace RhPhysicalNullOverlap
open RhWeightedMeasureEmbedding RhFlatSmoothCore RhPhysicalProjectionSchur
open RhFixedPhysicalSchurMatrix RhInwardOldNullLift RhPhysicalOverlapFinite

def liftedFamily {d : ℕ} {R : ℝ} (hR : 0 < R)
    (p : Fin d → FlatCoreSpace R) (r : Scale) : Fin d → FlatCoreSpace R :=
  fun j => oldNullLift hR r.property.1 (p j)

def overlapMatrix {d : ℕ} {R : ℝ} (hR : 0 < R)
    (p : Fin d → FlatCoreSpace R) (r : Scale) : Matrix (Fin d) (Fin d) ℝ :=
  overlap p (liftedFamily hR p r)

lemma physical_lift_tendsto {d : ℕ} {R : ℝ} (hR : 0 < R)
    (p : Fin d → FlatCoreSpace R) (j : Fin d) :
    Tendsto (fun r : Scale => physicalEmbedding (liftedFamily hR p r j : WeightedSpace))
      (𝓝 oneScale) (𝓝 (physicalEmbedding (p j : WeightedSpace))) := by
  have hc : Continuous (fun F : FlatCoreSpace R => physicalEmbedding (F : WeightedSpace)) :=
    physicalEmbedding.continuous.comp continuous_subtype_val
  simpa only [Function.comp_def, liftedFamily] using
    hc.continuousAt.tendsto.comp (oldNullLift_tendsto hR (p j))

/-- The literal actual physical overlap converges to the identity, not to a
postulated matrix. The old basis is explicitly physical-L2 orthonormal. -/
theorem actual_overlap_tendsto_identity {d : ℕ} {R : ℝ} (hR : 0 < R)
    (p : Fin d → FlatCoreSpace R)
    (hp : Orthonormal ℝ (fun i => physicalEmbedding (p i : WeightedSpace))) :
    Tendsto (overlapMatrix hR p) (𝓝 oneScale) (𝓝 1) :=
  overlap_tendsto_identity p hp (liftedFamily hR p) (physical_lift_tendsto hR p)

theorem actual_determinant_tendsto_one {d : ℕ} {R : ℝ} (hR : 0 < R)
    (p : Fin d → FlatCoreSpace R)
    (hp : Orthonormal ℝ (fun i => physicalEmbedding (p i : WeightedSpace))) :
    Tendsto (fun r : Scale => (overlapMatrix hR p r).det)
      (𝓝 oneScale) (𝓝 (1 : ℝ)) :=
  determinant_tendsto_one p hp (liftedFamily hR p) (physical_lift_tendsto hR p)

/-- Actual inward lifts have locally nonsingular physical coordinates and
their span projects onto EVERY prescribed physical old-basis coordinate. -/
theorem eventually_actual_span_surjective {d : ℕ} {R : ℝ} (hR : 0 < R)
    (p : Fin d → FlatCoreSpace R)
    (hp : Orthonormal ℝ (fun i => physicalEmbedding (p i : WeightedSpace))) :
    ∀ᶠ r : Scale in 𝓝 oneScale, (overlapMatrix hR p r).det ≠ 0 ∧
      ∀ a : Fin d → ℝ, ∃ F : FlatCoreSpace R,
        F ∈ Submodule.span ℝ (Set.range (liftedFamily hR p r)) ∧ coefficients p F = a :=
  eventually_invertible_and_surjective p hp (liftedFamily hR p) (physical_lift_tendsto hR p)

/-- The coordinate witness can be taken as the literal finite combination
of the actual lifted family. No abstract surjectivity oracle is assumed. -/
theorem eventually_actual_combination_surjective {d : ℕ} {R : ℝ} (hR : 0 < R)
    (p : Fin d → FlatCoreSpace R)
    (hp : Orthonormal ℝ (fun i => physicalEmbedding (p i : WeightedSpace))) :
    ∀ᶠ r : Scale in 𝓝 oneScale, (overlapMatrix hR p r).det ≠ 0 ∧
      ∀ a : Fin d → ℝ, ∃ c : Fin d → ℝ,
        coefficients p (combination (liftedFamily hR p r) c) = a := by
  filter_upwards [eventually_actual_span_surjective hR p hp] with r hr
  refine ⟨hr.1, ?_⟩
  have hu : IsUnit (overlapMatrix hR p r) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hr.1)
  have hs : Function.Surjective (overlapMatrix hR p r).mulVec :=
    Matrix.mulVec_surjective_iff_isUnit.mpr hu
  intro a
  obtain ⟨c, hc⟩ := hs a
  exact ⟨c, (RhPhysicalOverlapFinite.coefficients_combination p (liftedFamily hR p r) c).trans hc⟩

/-- An ordinary positive radius neighborhood, with the harmless local
restriction 1<=r<=2 spelled out. No numerical delta is extracted. -/
theorem exists_local_actual_coordinate_surjectivity {d : ℕ} {R : ℝ} (hR : 0 < R)
    (p : Fin d → FlatCoreSpace R)
    (hp : Orthonormal ℝ (fun i => physicalEmbedding (p i : WeightedSpace))) :
    ∃ delta > 0, ∀ (r : ℝ) (hr1 : 1 ≤ r) (hr2 : r ≤ 2), |r - 1| < delta →
      ∀ a : Fin d → ℝ, ∃ c : Fin d → ℝ,
        coefficients p (combination (fun j => oldNullLift hR hr1 (p j)) c) = a := by
  obtain ⟨delta, hdelta, hd⟩ :=
    Metric.eventually_nhds_iff.mp (eventually_actual_combination_surjective hR p hp)
  refine ⟨delta, hdelta, ?_⟩
  intro r hr1 hr2 hclose
  have hs : dist (⟨r, hr1, hr2⟩ : Scale) oneScale < delta := by
    simpa only [Subtype.dist_eq, Real.dist_eq, oneScale] using hclose
  exact (hd hs).2

end RhPhysicalNullOverlap
#print axioms RhPhysicalNullOverlap.actual_overlap_tendsto_identity
#print axioms RhPhysicalNullOverlap.actual_determinant_tendsto_one
#print axioms RhPhysicalNullOverlap.eventually_actual_span_surjective
#print axioms RhPhysicalNullOverlap.eventually_actual_combination_surjective
#print axioms RhPhysicalNullOverlap.exists_local_actual_coordinate_surjectivity
