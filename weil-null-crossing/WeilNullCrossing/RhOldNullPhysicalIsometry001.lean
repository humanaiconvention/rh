import RhInwardOldNullLift001

/-! The actual inward old-support lift is unitary ONLY in physical L2.
Its complete weighted graph norm is not asserted to be invariant.
-/
set_option maxHeartbeats 100000
set_option synthInstance.maxHeartbeats 20000
noncomputable section
open Set MeasureTheory
open scoped Topology
namespace RhOldNullPhysicalIsometry
open RhWeightedMeasureEmbedding RhFlatSmoothCore RhInwardOldNullLift

lemma oldNullLift_add {R r : ℝ} (hR : 0 < R) (hr : 1 ≤ r)
    (p q : FlatCoreSpace R) :
    oldNullLift hR hr (p+q) = oldNullLift hR hr p + oldNullLift hR hr q := by
  apply Subtype.ext
  change (RhFlatCoreDilation.inwardMap hr (p+q) : WeightedSpace) =
    ((RhFlatCoreDilation.inwardMap hr p : WeightedSpace) +
      (RhFlatCoreDilation.inwardMap hr q : WeightedSpace))
  exact congrArg (fun x : FlatCoreSpace (r⁻¹*R) => (x : WeightedSpace))
    ((RhFlatCoreDilation.inwardMap hr).map_add p q)

lemma oldNullLift_smul {R r : ℝ} (hR : 0 < R) (hr : 1 ≤ r)
    (c : ℝ) (p : FlatCoreSpace R) :
    oldNullLift hR hr (c • p) = c • oldNullLift hR hr p := by
  apply Subtype.ext
  change (RhFlatCoreDilation.inwardMap hr (c • p) : WeightedSpace) =
    c • (RhFlatCoreDilation.inwardMap hr p : WeightedSpace)
  exact congrArg (fun x : FlatCoreSpace (r⁻¹*R) => (x : WeightedSpace))
    ((RhFlatCoreDilation.inwardMap hr).map_smul c p)

/-- This is the norm of the actual physical complex L2 representative. -/
theorem physical_norm_square {R r : ℝ} (hR : 0 < R) (hr : 1 ≤ r)
    (p : FlatCoreSpace R) :
    ‖physicalEmbedding (oldNullLift hR hr p : WeightedSpace)‖ ^ 2 =
      ‖physicalEmbedding (p : WeightedSpace)‖ ^ 2 := by
  change ‖physicalEmbedding (RhWeightedDilationInverse.inwardLift hr
    (p : WeightedSpace) (flatCore_supported R p.property))‖ ^ 2 = _
  rw [RhWeightedDilationInverse.inwardLift_physical]
  exact RhWeightedDilation.dilatedPhysical_norm_square _ _ _

theorem physical_norm {R r : ℝ} (hR : 0 < R) (hr : 1 ≤ r)
    (p : FlatCoreSpace R) :
    ‖physicalEmbedding (oldNullLift hR hr p : WeightedSpace)‖ =
      ‖physicalEmbedding (p : WeightedSpace)‖ := by
  nlinarith [physical_norm_square hR hr p,
    norm_nonneg (physicalEmbedding (oldNullLift hR hr p : WeightedSpace)),
    norm_nonneg (physicalEmbedding (p : WeightedSpace))]

/-- Exact real Hilbert product, not a graph-norm polarization. -/
theorem physical_inner {R r : ℝ} (hR : 0 < R) (hr : 1 ≤ r)
    (p q : FlatCoreSpace R) :
    inner ℝ (physicalEmbedding (oldNullLift hR hr p : WeightedSpace))
      (physicalEmbedding (oldNullLift hR hr q : WeightedSpace)) =
    inner ℝ (physicalEmbedding (p : WeightedSpace))
      (physicalEmbedding (q : WeightedSpace)) := by
  have hsum := physical_norm_square hR hr (p+q)
  have hp := physical_norm_square hR hr p
  have hq := physical_norm_square hR hr q
  rw [oldNullLift_add] at hsum
  change ‖physicalEmbedding ((oldNullLift hR hr p : WeightedSpace) +
      (oldNullLift hR hr q : WeightedSpace))‖ ^ 2 =
    ‖physicalEmbedding ((p : WeightedSpace) + (q : WeightedSpace))‖ ^ 2 at hsum
  rw [map_add, map_add, norm_add_sq_real, norm_add_sq_real] at hsum
  linarith

/-- Prescribed physical orthonormal families retain their exact Gram matrix. -/
theorem physical_orthonormal {ι : Type*} {R r : ℝ} (hR : 0 < R) (hr : 1 ≤ r)
    (p : ι → FlatCoreSpace R)
    (hp : Orthonormal ℝ (fun i => physicalEmbedding (p i : WeightedSpace))) :
    Orthonormal ℝ (fun i => physicalEmbedding (oldNullLift hR hr (p i) : WeightedSpace)) := by
  classical
  rw [orthonormal_iff_ite] at hp ⊢
  intro i j
  rw [physical_inner hR hr, hp i j]

end RhOldNullPhysicalIsometry
#print axioms RhOldNullPhysicalIsometry.oldNullLift_add
#print axioms RhOldNullPhysicalIsometry.oldNullLift_smul
#print axioms RhOldNullPhysicalIsometry.physical_norm_square
#print axioms RhOldNullPhysicalIsometry.physical_norm
#print axioms RhOldNullPhysicalIsometry.physical_inner
#print axioms RhOldNullPhysicalIsometry.physical_orthonormal
