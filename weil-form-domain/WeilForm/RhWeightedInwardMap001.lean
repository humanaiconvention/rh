import RhWeightedDilationMap001
import RhWeightedDilationInverse001

/-! Genuine bounded inward real linear map on complete supported weighted
spaces, with its exact inverse identities against outward dilation. -/
noncomputable section
open Set MeasureTheory Filter FourierTransform
open scoped Topology ENNReal
namespace RhWeightedInwardMap
open RhDilation RhWeightedMeasureEmbedding RhWeightedDilation RhWeightedDilationMap
open RhWeightedDilationInverse

lemma inwardLift_add {R r : ℝ} (hr : 1 ≤ r) (F G : WeightedSpace)
    (hF : F ∈ supportedSubspace R) (hG : G ∈ supportedSubspace R) :
    inwardLift hr (F + G) ((supportedSubspace R).add_mem hF hG) =
      inwardLift hr F hF + inwardLift hr G hG := by
  apply physicalEmbedding_injective
  rw [map_add]
  apply Lp.ext
  have hin := complexDilate_add_ae (inv_pos.mpr (by linarith : 0 < r))
    (physicalEmbedding F) (physicalEmbedding G)
  have hout := inwardLift_physical_ae hr (F + G) ((supportedSubspace R).add_mem hF hG)
  rw [map_add] at hout
  filter_upwards [hout, hin, inwardLift_physical_ae hr F hF,
    inwardLift_physical_ae hr G hG,
    Lp.coeFn_add (physicalEmbedding (inwardLift hr F hF))
      (physicalEmbedding (inwardLift hr G hG))] with t hleft hadd hf hg hright
  rw [hleft, hadd, hright]
  dsimp only [Pi.add_apply]
  rw [hf, hg]

lemma inwardLift_real_smul {R r : ℝ} (hr : 1 ≤ r) (c : ℝ) (F : WeightedSpace)
    (hF : F ∈ supportedSubspace R) :
    inwardLift hr (c • F) ((supportedSubspace R).smul_mem c hF) = c • inwardLift hr F hF := by
  apply physicalEmbedding_injective
  rw [map_smul]
  apply Lp.ext
  have hin := complexDilate_real_smul_ae (inv_pos.mpr (by linarith : 0 < r)) c (physicalEmbedding F)
  have hout := inwardLift_physical_ae hr (c • F) ((supportedSubspace R).smul_mem c hF)
  rw [map_smul] at hout
  filter_upwards [hout, hin, inwardLift_physical_ae hr F hF,
    Lp.coeFn_smul c (physicalEmbedding (inwardLift hr F hF))] with t hleft hscalar hf hright
  rw [hleft, hscalar, hright]
  dsimp only [Pi.smul_apply]
  rw [hf]

def inwardLinear {R r : ℝ} (hr : 1 ≤ r) : SupportedSpace R →ₗ[ℝ] SupportedSpace (r⁻¹ * R) where
  toFun F := ⟨inwardLift hr F F.property, inwardLift_supported hr F F.property⟩
  map_add' F G := by
    apply Subtype.ext
    exact inwardLift_add hr F G F.property G.property
  map_smul' c F := by
    apply Subtype.ext
    exact inwardLift_real_smul hr c F F.property

/-- The norm bound is the square root of the exact 1+5 log r native budget. -/
def inwardMap {R r : ℝ} (hr : 1 ≤ r) :
    SupportedSpace R →L[ℝ] SupportedSpace (r⁻¹ * R) :=
  (inwardLinear (R := R) hr).mkContinuous (Real.sqrt (1 + 5 * Real.log r)) (fun F => by
    change ‖inwardLift hr (F : WeightedSpace) F.property‖ ≤
      Real.sqrt (1 + 5 * Real.log r) * ‖(F : WeightedSpace)‖
    exact inwardLift_norm_le hr F F.property)

lemma inwardMap_norm_le {R r : ℝ} (hr : 1 ≤ r) (F : SupportedSpace R) :
    ‖inwardMap hr F‖ ≤ Real.sqrt (1 + 5 * Real.log r) * ‖F‖ :=
  inwardLift_norm_le hr F F.property

lemma inwardMap_physical_ae {R r : ℝ} (hr : 1 ≤ r) (F : SupportedSpace R) :
    physicalEmbedding (inwardMap hr F : WeightedSpace) =ᵐ[volume]
      complexDilate r⁻¹ (physicalEmbedding (F : WeightedSpace)) :=
  inwardLift_physical_ae hr F F.property

/-- Equality is stated in the common ambient weighted space so no false
judgmental equality of the two algebraically equal support radii is assumed. -/
lemma inwardMap_outwardMap_cancel {R r : ℝ} (hr : 1 ≤ r) (F : SupportedSpace R) :
    (inwardMap hr (outwardMap hr F) : WeightedSpace) = (F : WeightedSpace) :=
  inward_outward_cancel hr F F.property

lemma outwardMap_inwardMap_cancel {R r : ℝ} (hr : 1 ≤ r) (F : SupportedSpace R) :
    (outwardMap hr (inwardMap hr F) : WeightedSpace) = (F : WeightedSpace) :=
  outward_inward_cancel hr F F.property

end RhWeightedInwardMap
#print axioms RhWeightedInwardMap.inwardLift_add
#print axioms RhWeightedInwardMap.inwardLift_real_smul
#print axioms RhWeightedInwardMap.inwardMap_norm_le
#print axioms RhWeightedInwardMap.inwardMap_physical_ae
#print axioms RhWeightedInwardMap.inwardMap_outwardMap_cancel
#print axioms RhWeightedInwardMap.outwardMap_inwardMap_cancel
