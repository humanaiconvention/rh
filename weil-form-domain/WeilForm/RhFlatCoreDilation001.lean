import RhFlatSmoothCore001
import RhClosedCoreDilationInverse001

/-! Actual outward and inward complete-norm dilation on the SAME flattened
closed smooth core. Membership uses the proved exact nested-image equality;
no smooth-domain equality or physical regularity hypothesis is introduced.
-/
noncomputable section
open Set MeasureTheory Filter FourierTransform
open scoped Topology ENNReal
namespace RhFlatCoreDilation
open RhWeightedMeasureEmbedding RhWeightedDilation RhWeightedDilationInverse
open RhFlatSmoothCore

lemma outward_mem {R r : ℝ} (hr : 1 ≤ r) {F : WeightedSpace}
    (hF : F ∈ flatCore R) :
    outwardLift hr F (flatCore_supported R hF) ∈ flatCore (r * R) := by
  have hi : F ∈ nestedImage R := by rw [← flatCore_eq_nestedImage]; exact hF
  rcases hi with ⟨X, hX, rfl⟩
  exact nested_core_mem_flat (RhClosedCoreDilation.outward_preserves_core hr hX)

lemma inward_mem {R r : ℝ} (hr : 1 ≤ r) {F : WeightedSpace}
    (hF : F ∈ flatCore R) :
    inwardLift hr F (flatCore_supported R hF) ∈ flatCore (r⁻¹ * R) := by
  have hi : F ∈ nestedImage R := by rw [← flatCore_eq_nestedImage]; exact hF
  rcases hi with ⟨X, hX, rfl⟩
  exact nested_core_mem_flat (RhClosedCoreDilationInverse.inward_preserves_core hr hX)

def outwardLinear {R r : ℝ} (hr : 1 ≤ r) : FlatCoreSpace R →ₗ[ℝ] FlatCoreSpace (r * R) where
  toFun F := ⟨outwardLift hr F (flatCore_supported R F.property), outward_mem hr F.property⟩
  map_add' F G := by
    apply Subtype.ext
    exact RhWeightedDilationMap.outwardLift_add hr F G
      (flatCore_supported R F.property) (flatCore_supported R G.property)
  map_smul' c F := by
    apply Subtype.ext
    exact RhWeightedDilationMap.outwardLift_real_smul hr c F (flatCore_supported R F.property)

def outwardMap {R r : ℝ} (hr : 1 ≤ r) : FlatCoreSpace R →L[ℝ] FlatCoreSpace (r * R) :=
  (outwardLinear (R := R) hr).mkContinuous 1 (fun F => by
    change ‖outwardLift hr (F : WeightedSpace) (flatCore_supported R F.property)‖ ≤
      1 * ‖(F : WeightedSpace)‖
    simpa only [one_mul] using outwardLift_norm_le hr F (flatCore_supported R F.property))

def inwardLinear {R r : ℝ} (hr : 1 ≤ r) : FlatCoreSpace R →ₗ[ℝ] FlatCoreSpace (r⁻¹ * R) where
  toFun F := ⟨inwardLift hr F (flatCore_supported R F.property), inward_mem hr F.property⟩
  map_add' F G := by
    apply Subtype.ext
    exact RhWeightedInwardMap.inwardLift_add hr F G
      (flatCore_supported R F.property) (flatCore_supported R G.property)
  map_smul' c F := by
    apply Subtype.ext
    exact RhWeightedInwardMap.inwardLift_real_smul hr c F (flatCore_supported R F.property)

def inwardMap {R r : ℝ} (hr : 1 ≤ r) : FlatCoreSpace R →L[ℝ] FlatCoreSpace (r⁻¹ * R) :=
  (inwardLinear (R := R) hr).mkContinuous (Real.sqrt (1 + 5 * Real.log r)) (fun F => by
    exact inwardLift_norm_le hr F (flatCore_supported R F.property))

lemma outwardMap_norm_le {R r : ℝ} (hr : 1 ≤ r) (F : FlatCoreSpace R) :
    ‖outwardMap hr F‖ ≤ ‖F‖ :=
  outwardLift_norm_le hr F (flatCore_supported R F.property)

lemma inwardMap_norm_le {R r : ℝ} (hr : 1 ≤ r) (F : FlatCoreSpace R) :
    ‖inwardMap hr F‖ ≤ Real.sqrt (1 + 5 * Real.log r) * ‖F‖ :=
  inwardLift_norm_le hr F (flatCore_supported R F.property)

lemma outwardMap_physical_ae {R r : ℝ} (hr : 1 ≤ r) (F : FlatCoreSpace R) :
    physicalEmbedding (outwardMap hr F : WeightedSpace) =ᵐ[volume]
      RhDilation.complexDilate r (physicalEmbedding (F : WeightedSpace)) :=
  outwardLift_physical_ae hr F (flatCore_supported R F.property)

lemma inwardMap_physical_ae {R r : ℝ} (hr : 1 ≤ r) (F : FlatCoreSpace R) :
    physicalEmbedding (inwardMap hr F : WeightedSpace) =ᵐ[volume]
      RhDilation.complexDilate r⁻¹ (physicalEmbedding (F : WeightedSpace)) :=
  inwardLift_physical_ae hr F (flatCore_supported R F.property)

lemma inward_outward_cancel {R r : ℝ} (hr : 1 ≤ r) (F : FlatCoreSpace R) :
    (inwardMap hr (outwardMap hr F) : WeightedSpace) = (F : WeightedSpace) :=
  RhWeightedDilationInverse.inward_outward_cancel hr F (flatCore_supported R F.property)

lemma outward_inward_cancel {R r : ℝ} (hr : 1 ≤ r) (F : FlatCoreSpace R) :
    (outwardMap hr (inwardMap hr F) : WeightedSpace) = (F : WeightedSpace) :=
  RhWeightedDilationInverse.outward_inward_cancel hr F (flatCore_supported R F.property)

def radiusCast {R S : ℝ} (h : R = S) : FlatCoreSpace R →L[ℝ] FlatCoreSpace S := by
  subst S
  exact ContinuousLinearMap.id ℝ (FlatCoreSpace R)

lemma radiusCast_ambient {R S : ℝ} (h : R = S) (F : FlatCoreSpace R) :
    (radiusCast h F : WeightedSpace) = (F : WeightedSpace) := by subst S; rfl

lemma radiusCast_norm {R S : ℝ} (h : R = S) (F : FlatCoreSpace R) :
    ‖radiusCast h F‖ = ‖F‖ := by subst S; rfl

lemma inverse_radius {R r : ℝ} (hr : 1 ≤ r) : r⁻¹ * (r * R) = R := by
  have hn : r ≠ 0 := (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hr).ne'
  rw [← mul_assoc, inv_mul_cancel₀ hn, one_mul]

def returnMap {R r : ℝ} (hr : 1 ≤ r) : FlatCoreSpace (r * R) →L[ℝ] FlatCoreSpace R :=
  (radiusCast (inverse_radius (R := R) hr)).comp (inwardMap hr)

lemma outward_ambient_congr {R S r : ℝ} (hr : 1 ≤ r)
    (F : FlatCoreSpace R) (G : FlatCoreSpace S) (h : (F : WeightedSpace) = (G : WeightedSpace)) :
    (outwardMap hr F : WeightedSpace) = (outwardMap hr G : WeightedSpace) := by
  apply physicalEmbedding_injective
  apply Lp.ext
  have hf := outwardMap_physical_ae hr F
  have hg := outwardMap_physical_ae hr G
  rw [h] at hf
  exact hf.trans hg.symm

theorem return_outward_cancel {R r : ℝ} (hr : 1 ≤ r) (F : FlatCoreSpace R) :
    returnMap hr (outwardMap hr F) = F := by
  apply Subtype.ext
  change (radiusCast (inverse_radius (R := R) hr) (inwardMap hr (outwardMap hr F)) : WeightedSpace) = _
  rw [radiusCast_ambient]
  exact inward_outward_cancel hr F

theorem outward_return_cancel {R r : ℝ} (hr : 1 ≤ r) (F : FlatCoreSpace (r * R)) :
    outwardMap hr (returnMap hr F) = F := by
  apply Subtype.ext
  have hc := radiusCast_ambient (inverse_radius (R := R) hr) (inwardMap hr F)
  have h := outward_ambient_congr hr (returnMap hr F) (inwardMap hr F) hc
  exact h.trans (outward_inward_cancel hr F)

def dilationEquiv {R r : ℝ} (hr : 1 ≤ r) : FlatCoreSpace R ≃L[ℝ] FlatCoreSpace (r * R) where
  toLinearEquiv :=
    { (outwardMap hr).toLinearMap with
      invFun := returnMap hr
      left_inv := return_outward_cancel hr
      right_inv := outward_return_cancel hr }
  continuous_toFun := (outwardMap hr).continuous
  continuous_invFun := (returnMap hr).continuous

end RhFlatCoreDilation
#print axioms RhFlatCoreDilation.outward_mem
#print axioms RhFlatCoreDilation.inward_mem
#print axioms RhFlatCoreDilation.outwardMap_norm_le
#print axioms RhFlatCoreDilation.inwardMap_norm_le
#print axioms RhFlatCoreDilation.return_outward_cancel
#print axioms RhFlatCoreDilation.outward_return_cancel
#print axioms RhFlatCoreDilation.dilationEquiv
