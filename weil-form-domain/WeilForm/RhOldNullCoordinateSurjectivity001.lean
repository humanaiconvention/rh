import RhPhysicalNullOverlap001
import RhInwardOldNullSubspace001

/-! Actual physical-coordinate surjectivity on the inward image of the true
native form radical. Null membership and physical orthonormality are explicit;
all continuity and determinant hypotheses are supplied by actual dilation.
No nontrivial nullspace, complement gap, or residual sign is asserted.
-/
set_option maxHeartbeats 100000
set_option synthInstance.maxHeartbeats 20000
noncomputable section
open Set Filter
open scoped Topology BigOperators
namespace RhOldNullCoordinateSurjectivity
open RhWeightedMeasureEmbedding RhFlatSmoothCore RhPhysicalProjectionSchur
open RhInwardOldNullLift RhInwardOldNullSubspace RhPhysicalNullOverlap

lemma lifted_span_le_outward_null {d : ℕ} {R : ℝ} (hR : 0 < R)
    (C : ℝ) (N : ℕ) (p : Fin d → FlatCoreSpace R)
    (hp : ∀ i, p i ∈ baseNullSpace R C N) (r : Scale) :
    Submodule.span ℝ (Set.range (liftedFamily hR p r)) ≤
      outwardOldNullSpace hR r.property.1 C N := by
  apply Submodule.span_le.mpr
  rintro F ⟨i, rfl⟩
  change oldNullLift hR r.property.1 (p i) ∈ outwardOldNullSpace hR r.property.1 C N
  exact lift_mem_outwardOldNullSpace hR r.property.1 C N (p i) (hp i)

/-- A genuine locally surjective projection from the ACTUAL isotropic
subspace W_r onto the prescribed old physical coordinates. -/
theorem eventually_physical_coordinates_surjective {d : ℕ} {R : ℝ} (hR : 0 < R)
    (C : ℝ) (N : ℕ) (p : Fin d → FlatCoreSpace R)
    (hp : Orthonormal ℝ (fun i => physicalEmbedding (p i : WeightedSpace)))
    (hn : ∀ i, p i ∈ baseNullSpace R C N) :
    ∀ᶠ r : Scale in 𝓝 oneScale,
      Function.Surjective (fun w : outwardOldNullSpace hR r.property.1 C N =>
        coefficients p (w : FlatCoreSpace R)) := by
  filter_upwards [eventually_actual_span_surjective hR p hp] with r hr
  intro a
  obtain ⟨F, hF, hcoeff⟩ := hr.2 a
  exact ⟨⟨F, lifted_span_le_outward_null hR C N p hn r hF⟩, hcoeff⟩

/-- Ordinary outward-radius locality, with no assumed invertible matrix or
assumed source projection. The proof also covers the empty family. -/
theorem exists_local_physical_coordinates_surjective {d : ℕ} {R : ℝ} (hR : 0 < R)
    (C : ℝ) (N : ℕ) (p : Fin d → FlatCoreSpace R)
    (hp : Orthonormal ℝ (fun i => physicalEmbedding (p i : WeightedSpace)))
    (hn : ∀ i, p i ∈ baseNullSpace R C N) :
    ∃ delta > 0, ∀ r : Scale, |(r : ℝ) - 1| < delta →
      Function.Surjective (fun w : outwardOldNullSpace hR r.property.1 C N =>
        coefficients p (w : FlatCoreSpace R)) := by
  obtain ⟨delta, hdelta, hd⟩ := Metric.eventually_nhds_iff.mp
    (eventually_physical_coordinates_surjective hR C N p hp hn)
  refine ⟨delta, hdelta, ?_⟩
  intro r hclose
  have hs : dist r oneScale < delta := by
    simpa only [Subtype.dist_eq, Real.dist_eq, oneScale] using hclose
  exact hd hs

end RhOldNullCoordinateSurjectivity
#print axioms RhOldNullCoordinateSurjectivity.lifted_span_le_outward_null
#print axioms RhOldNullCoordinateSurjectivity.eventually_physical_coordinates_surjective
#print axioms RhOldNullCoordinateSurjectivity.exists_local_physical_coordinates_surjective

