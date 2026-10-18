import RhPulledCompleteForm001
import RhPhysicalOrthogonalSchur001

/-! Actual inclusion of the fixed physical-L2 complement into the base real
form core. The inclusion is explicitly typed to avoid an inferred module
instance diamond; no Hilbert norm is changed. -/
set_option maxHeartbeats 0
noncomputable section
open Set MeasureTheory
open scoped Topology
namespace RhFixedPhysicalPulledSchur
open RhWeightedMeasureEmbedding RhFlatSmoothCore RhPhysicalOrthogonalSchur

def toCoreLinear {d : ℕ} (R : ℝ) (p : Fin d → FlatCoreSpace R) :
    ComplementSpace R p →ₗ[ℝ] FlatCoreSpace R where
  toFun q := ⟨(q : WeightedSpace), (show complement R p ≤ flatCore R from inf_le_left) q.property⟩
  map_add' x y := by apply Subtype.ext; rfl
  map_smul' c x := by apply Subtype.ext; rfl

def toCore {d : ℕ} (R : ℝ) (p : Fin d → FlatCoreSpace R) :
    ComplementSpace R p →L[ℝ] FlatCoreSpace R :=
  (toCoreLinear R p).mkContinuous 1 (fun q => by
    change ‖(q : WeightedSpace)‖ ≤ 1 * ‖(q : WeightedSpace)‖
    simpa only [one_mul] using (le_refl ‖(q : WeightedSpace)‖))

lemma toCore_ambient {d : ℕ} (R : ℝ) (p : Fin d → FlatCoreSpace R)
    (q : ComplementSpace R p) : (toCore R p q : WeightedSpace) = (q : WeightedSpace) := rfl

lemma toCore_norm {d : ℕ} (R : ℝ) (p : Fin d → FlatCoreSpace R)
    (q : ComplementSpace R p) : ‖toCore R p q‖ = ‖q‖ := rfl

end RhFixedPhysicalPulledSchur
#print axioms RhFixedPhysicalPulledSchur.toCore_ambient
#print axioms RhFixedPhysicalPulledSchur.toCore_norm
