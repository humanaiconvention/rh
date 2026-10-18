import RhInwardOldNullLift001

/-! Construct the actual inward image of the actual complete-form radical.
This is a bounded injective map and an actual outward-isotropic subspace;
no nullspace existence, nontriviality, dimension or positive gap is assumed. -/
set_option maxHeartbeats 100000
set_option synthInstance.maxHeartbeats 20000
noncomputable section
open Set MeasureTheory Filter
open scoped Topology BigOperators
namespace RhInwardOldNullSubspace
open RhWeightedMeasureEmbedding RhFlatSmoothCore RhPulledCompleteForm
open RhInwardOldNullLift

def oldNullLinear {R r : ℝ} (hR : 0 < R) (hr : 1 ≤ r) :
    FlatCoreSpace R →ₗ[ℝ] FlatCoreSpace R where
  toFun p := oldNullLift hR hr p
  map_add' p q := by
    apply Subtype.ext
    change (RhFlatCoreDilation.inwardMap hr (p + q) : WeightedSpace) =
      (RhFlatCoreDilation.inwardMap hr p : WeightedSpace) +
        (RhFlatCoreDilation.inwardMap hr q : WeightedSpace)
    exact congrArg (fun F : FlatCoreSpace (r⁻¹ * R) => (F : WeightedSpace))
      ((RhFlatCoreDilation.inwardMap hr).map_add p q)
  map_smul' c p := by
    apply Subtype.ext
    change (RhFlatCoreDilation.inwardMap hr (c • p) : WeightedSpace) =
      c • (RhFlatCoreDilation.inwardMap hr p : WeightedSpace)
    exact congrArg (fun F : FlatCoreSpace (r⁻¹ * R) => (F : WeightedSpace))
      ((RhFlatCoreDilation.inwardMap hr).map_smul c p)

def oldNullMap {R r : ℝ} (hR : 0 < R) (hr : 1 ≤ r) :
    FlatCoreSpace R →L[ℝ] FlatCoreSpace R :=
  (oldNullLinear hR hr).mkContinuous (Real.sqrt (1 + 5 * Real.log r)) (fun p => by
    change ‖(RhFlatCoreDilation.inwardMap hr p : WeightedSpace)‖ ≤
      Real.sqrt (1 + 5 * Real.log r) * ‖p‖
    exact RhFlatCoreDilation.inwardMap_norm_le hr p)

lemma oldNullMap_apply {R r : ℝ} (hR : 0 < R) (hr : 1 ≤ r) (p : FlatCoreSpace R) :
    oldNullMap hR hr p = oldNullLift hR hr p := rfl

theorem oldNullMap_injective {R r : ℝ} (hR : 0 < R) (hr : 1 ≤ r) :
    Function.Injective (oldNullMap hR hr) := by
  intro p q hpq
  apply Subtype.ext
  have he := congrArg (fun w : FlatCoreSpace R =>
    (RhFlatCoreDilation.outwardMap hr w : WeightedSpace)) hpq
  simpa only [oldNullMap_apply, outward_oldNullLift_ambient] using he

/-- The actual full form radical, not a declared spectral-coordinate list. -/
def baseNullSpace (R C : ℝ) (N : ℕ) : Submodule ℝ (FlatCoreSpace R) :=
  (baseForm R C N).ker

/-- Actual W_r = inward(old complete-form radical), followed by literal
inclusion into the fixed core. This definition includes the trivial case. -/
def outwardOldNullSpace {R r : ℝ} (hR : 0 < R) (hr : 1 ≤ r) (C : ℝ) (N : ℕ) :
    Submodule ℝ (FlatCoreSpace R) :=
  (baseNullSpace R C N).map (oldNullLinear hR hr)

theorem lift_mem_outwardOldNullSpace {R r : ℝ} (hR : 0 < R) (hr : 1 ≤ r)
    (C : ℝ) (N : ℕ) (p : FlatCoreSpace R) (hp : p ∈ baseNullSpace R C N) :
    oldNullLift hR hr p ∈ outwardOldNullSpace hR hr C N :=
  ⟨p, hp, rfl⟩

/-- Exact complete pair annihilation on the constructed W_r, retaining the
ENTIRE arithmetic form. It is not a claim that cross-pairings with arbitrary
outside vectors vanish. -/
theorem outwardOldNullSpace_pair_zero {R r : ℝ} (hR : 0 < R) (hr : 1 ≤ r)
    (C : ℝ) (N : ℕ) (w z : outwardOldNullSpace hR hr C N) :
    pulledForm hr C N (w : FlatCoreSpace R) (z : FlatCoreSpace R) = 0 := by
  rcases w.property with ⟨p, hp, hpw⟩
  rcases z.property with ⟨q, hq, hqz⟩
  rw [← hpw, ← hqz]
  change pulledForm hr C N (oldNullLift hR hr p) (oldNullLift hR hr q) = 0
  rw [pulledForm_oldNullLift_pair hR hr C N]
  have hp0 : baseForm R C N p = 0 := hp
  simpa only [ContinuousLinearMap.zero_apply] using
    congrArg (fun L : FlatCoreSpace R →L[ℝ] ℝ => L q) hp0

theorem outwardOldNullSpace_diagonal_zero {R r : ℝ} (hR : 0 < R) (hr : 1 ≤ r)
    (C : ℝ) (N : ℕ) (w : outwardOldNullSpace hR hr C N) :
    pulledForm hr C N (w : FlatCoreSpace R) (w : FlatCoreSpace R) = 0 :=
  outwardOldNullSpace_pair_zero hR hr C N w w

end RhInwardOldNullSubspace
#print axioms RhInwardOldNullSubspace.oldNullMap_injective
#print axioms RhInwardOldNullSubspace.lift_mem_outwardOldNullSpace
#print axioms RhInwardOldNullSubspace.outwardOldNullSpace_pair_zero
#print axioms RhInwardOldNullSubspace.outwardOldNullSpace_diagonal_zero