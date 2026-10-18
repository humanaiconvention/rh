import RhWeightedDilation001

/-! The actual outward map as a contractive continuous real linear map between
supported complete form spaces. Linearity is reconstructed in physical L2
using nonsingular AE pullback, not postulated for representative values. -/
noncomputable section
open Set MeasureTheory Filter FourierTransform
open scoped Topology ENNReal
namespace RhWeightedDilationMap
open RhDilation RhWeightedMeasureEmbedding RhWeightedDilation

lemma complexDilate_add_ae {r : ℝ} (hr : 0 < r) (u v : WholeSpace) :
    complexDilate r (u + v : WholeSpace) =ᵐ[volume] fun t => complexDilate r u t + complexDilate r v t := by
  filter_upwards [ae_comp_div hr (Lp.coeFn_add u v)] with t ht
  simp only [complexDilate, ht, Pi.add_apply]
  ring

lemma complexDilate_real_smul_ae {r : ℝ} (hr : 0 < r) (c : ℝ) (u : WholeSpace) :
    complexDilate r (c • u : WholeSpace) =ᵐ[volume] fun t => c • complexDilate r u t := by
  filter_upwards [ae_comp_div hr (Lp.coeFn_smul c u)] with t ht
  simp only [complexDilate, ht, Pi.smul_apply, Complex.real_smul]
  ring

lemma outwardLift_add {R r : ℝ} (hr : 1 ≤ r) (F G : WeightedSpace)
    (hF : F ∈ supportedSubspace R) (hG : G ∈ supportedSubspace R) :
    outwardLift hr (F + G) ((supportedSubspace R).add_mem hF hG) =
      outwardLift hr F hF + outwardLift hr G hG := by
  apply physicalEmbedding_injective
  rw [map_add]
  apply Lp.ext
  have hin := complexDilate_add_ae (by linarith : 0 < r) (physicalEmbedding F) (physicalEmbedding G)
  have hout := outwardLift_physical_ae hr (F + G) ((supportedSubspace R).add_mem hF hG)
  rw [map_add] at hout
  filter_upwards [hout, hin, outwardLift_physical_ae hr F hF,
    outwardLift_physical_ae hr G hG,
    Lp.coeFn_add (physicalEmbedding (outwardLift hr F hF))
      (physicalEmbedding (outwardLift hr G hG))] with t hleft hadd hf hg hright
  rw [hleft, hadd, hright]
  dsimp only [Pi.add_apply]
  rw [hf, hg]

lemma outwardLift_real_smul {R r : ℝ} (hr : 1 ≤ r) (c : ℝ) (F : WeightedSpace)
    (hF : F ∈ supportedSubspace R) :
    outwardLift hr (c • F) ((supportedSubspace R).smul_mem c hF) = c • outwardLift hr F hF := by
  apply physicalEmbedding_injective
  rw [map_smul]
  apply Lp.ext
  have hin := complexDilate_real_smul_ae (by linarith : 0 < r) c (physicalEmbedding F)
  have hout := outwardLift_physical_ae hr (c • F) ((supportedSubspace R).smul_mem c hF)
  rw [map_smul] at hout
  filter_upwards [hout, hin, outwardLift_physical_ae hr F hF,
    Lp.coeFn_smul c (physicalEmbedding (outwardLift hr F hF))] with t hleft hscalar hf hright
  rw [hleft, hscalar, hright]
  dsimp only [Pi.smul_apply]
  rw [hf]

/-- Actual outward dilation as a real linear map of complete supported spaces. -/
def outwardLinear {R r : ℝ} (hr : 1 ≤ r) : SupportedSpace R →ₗ[ℝ] SupportedSpace (r * R) where
  toFun F := ⟨outwardLift hr F F.property, outwardLift_supported hr F F.property⟩
  map_add' F G := by
    apply Subtype.ext
    exact outwardLift_add hr F G F.property G.property
  map_smul' c F := by
    apply Subtype.ext
    exact outwardLift_real_smul hr c F F.property

/-- Complete norm contractivity supplies the genuine continuous extension. -/
def outwardMap {R r : ℝ} (hr : 1 ≤ r) : SupportedSpace R →L[ℝ] SupportedSpace (r * R) :=
  (outwardLinear (R := R) hr).mkContinuous 1 (fun F => by
    change ‖outwardLift hr (F : WeightedSpace) F.property‖ ≤ 1 * ‖(F : WeightedSpace)‖
    simpa only [one_mul] using outwardLift_norm_le hr (F : WeightedSpace) F.property)

lemma outwardMap_norm_le {R r : ℝ} (hr : 1 ≤ r) (F : SupportedSpace R) :
    ‖outwardMap hr F‖ ≤ ‖F‖ := outwardLift_norm_le hr F F.property

lemma outwardMap_physical_ae {R r : ℝ} (hr : 1 ≤ r) (F : SupportedSpace R) :
    physicalEmbedding (outwardMap hr F : WeightedSpace) =ᵐ[volume]
      complexDilate r (physicalEmbedding (F : WeightedSpace)) :=
  outwardLift_physical_ae hr F F.property

end RhWeightedDilationMap
#print axioms RhWeightedDilationMap.outwardLift_add
#print axioms RhWeightedDilationMap.outwardLift_real_smul
#print axioms RhWeightedDilationMap.outwardMap_norm_le
#print axioms RhWeightedDilationMap.outwardMap_physical_ae
