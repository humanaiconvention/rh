import RhDilationContraction001
import RhPhysicalShiftFourier001
import RhDilationPhysical001

/-! Outward dilation of arbitrary supported weighted Fourier vectors. Native
energy, support and normalization are proved for the actual L2 representatives;
no physical derivative or target perturbation estimate is assumed. -/
set_option maxHeartbeats 0
noncomputable section
open Set MeasureTheory Filter FourierTransform
open scoped Topology BigOperators ENNReal
namespace RhWeightedDilation
open RhAnchored RhDilation RhTail RhWeightedMeasureEmbedding RhWeightedEnergyIdentity
open RhDilationContraction

lemma ae_comp_div {r : ℝ} (hr : 0 < r) {p : ℝ → Prop} (hp : ∀ᵐ t ∂volume, p t) :
    ∀ᵐ t ∂volume, p (t / r) := by
  have hm : ∀ᵐ t ∂Measure.map (fun x : ℝ => r⁻¹ * x) volume, p t := by
    rw [Real.map_volume_mul_left (inv_ne_zero hr.ne')]
    exact Measure.ae_smul_measure hp _
  have h := ae_of_ae_map (measurable_const_mul r⁻¹).aemeasurable hm
  simpa only [div_eq_mul_inv, mul_comm] using h

/-- Exact spatial L2 dilation, formed from actual supported physical input. -/
def dilatedPhysical {R r : ℝ} (hr : 0 < r) (F : WeightedSpace)
    (hF : F ∈ supportedSubspace R) : RhWeightedMeasureEmbedding.WholeSpace :=
  (complexDilate_memLp hr (RhPhysicalShiftFourier.supported_integrable hF)
    (Lp.memLp (physicalEmbedding F))).toLp (complexDilate r (physicalEmbedding F))

lemma dilatedPhysical_ae {R r : ℝ} (hr : 0 < r) (F : WeightedSpace)
    (hF : F ∈ supportedSubspace R) :
    dilatedPhysical hr F hF =ᵐ[volume] complexDilate r (physicalEmbedding F) :=
  (complexDilate_memLp hr (RhPhysicalShiftFourier.supported_integrable hF)
    (Lp.memLp (physicalEmbedding F))).coeFn_toLp

/-- Support changes by the same exact positive factor as the spatial variable. -/
lemma dilatedPhysical_supported {R r : ℝ} (hr : 0 < r) (F : WeightedSpace)
    (hF : F ∈ supportedSubspace R) :
    ∀ᵐ t ∂volume, t ∉ Icc (-(r * R)) (r * R) → dilatedPhysical hr F hF t = 0 := by
  have hs := ae_comp_div hr ((mem_supportedSubspace_iff R F).mp hF)
  filter_upwards [dilatedPhysical_ae hr F hF, hs] with t ht hs
  intro hout
  have hin : t / r ∉ interval R := by
    intro hi
    exact hout ((mem_interval_div_iff hr R t).mp hi)
  rw [ht]
  simp only [complexDilate, hs hin, mul_zero]

lemma dilatedPhysical_norm_square {R r : ℝ} (hr : 0 < r) (F : WeightedSpace)
    (hF : F ∈ supportedSubspace R) :
    ‖dilatedPhysical hr F hF‖ ^ 2 = ‖physicalEmbedding F‖ ^ 2 := by
  simpa only [dilatedPhysical, Lp.toLp_coeFn] using
    complexDilate_L2_norm_square hr (RhPhysicalShiftFourier.supported_integrable hF)
      (Lp.memLp (physicalEmbedding F))

/-- Complete native energy contracts for outward dilation, before conversion to real. -/
lemma dilatedPhysical_energy_le {R r : ℝ} (hr : 1 ≤ r) (F : WeightedSpace)
    (hF : F ∈ supportedSubspace R) :
    fullFrequencyEnergy (1 / 2) (dilatedPhysical (by linarith : 0 < r) F hF) ≤
      fullFrequencyEnergy (1 / 2) (physicalEmbedding F) := by
  simpa only [dilatedPhysical, Lp.toLp_coeFn] using
    full_energy_contraction hr (by norm_num : (0 : ℝ) < 1 / 2)
      (RhPhysicalShiftFourier.supported_integrable hF) (Lp.memLp (physicalEmbedding F))

lemma dilatedPhysical_energy_finite {R r : ℝ} (hr : 1 ≤ r) (F : WeightedSpace)
    (hF : F ∈ supportedSubspace R) :
    fullFrequencyEnergy (1 / 2) (dilatedPhysical (by linarith : 0 < r) F hF) < ⊤ :=
  lt_of_le_of_lt (dilatedPhysical_energy_le hr F hF) (weighted_native_energy_finite F)

/-- Actual frequency-space lift of the spatially dilated input. -/
def outwardLift {R r : ℝ} (hr : 1 ≤ r) (F : WeightedSpace)
    (hF : F ∈ supportedSubspace R) : WeightedSpace :=
  frequencyLift (dilatedPhysical (by linarith : 0 < r) F hF)
    (dilatedPhysical_energy_finite hr F hF)

lemma outwardLift_physical {R r : ℝ} (hr : 1 ≤ r) (F : WeightedSpace)
    (hF : F ∈ supportedSubspace R) :
    physicalEmbedding (outwardLift hr F hF) =
      dilatedPhysical (by linarith : 0 < r) F hF :=
  physicalEmbedding_frequencyLift _ _

lemma outwardLift_physical_ae {R r : ℝ} (hr : 1 ≤ r) (F : WeightedSpace)
    (hF : F ∈ supportedSubspace R) :
    physicalEmbedding (outwardLift hr F hF) =ᵐ[volume]
      complexDilate r (physicalEmbedding F) := by
  rw [outwardLift_physical]
  exact dilatedPhysical_ae _ F hF

lemma outwardLift_supported {R r : ℝ} (hr : 1 ≤ r) (F : WeightedSpace)
    (hF : F ∈ supportedSubspace R) :
    outwardLift hr F hF ∈ supportedSubspace (r * R) :=
  frequencyLift_mem_supportedSubspace (r * R) _ _
    (dilatedPhysical_supported (by linarith : 0 < r) F hF)

/-- Contractive bound in the complete actual weighted norm, not merely L2. -/
theorem outwardLift_norm_le {R r : ℝ} (hr : 1 ≤ r) (F : WeightedSpace)
    (hF : F ∈ supportedSubspace R) : ‖outwardLift hr F hF‖ ≤ ‖F‖ := by
  have hE : (fullFrequencyEnergy (1 / 2)
      (dilatedPhysical (by linarith : 0 < r) F hF)).toReal ≤
      (fullFrequencyEnergy (1 / 2) (physicalEmbedding F)).toReal :=
    ENNReal.toReal_mono (weighted_native_energy_finite F).ne (dilatedPhysical_energy_le hr F hF)
  have hnorm : ‖outwardLift hr F hF‖ ^ 2 ≤ ‖F‖ ^ 2 := by
    rw [outwardLift, frequencyLift_norm_square, dilatedPhysical_norm_square,
      weighted_norm_square F]
    linarith
  nlinarith [norm_nonneg (outwardLift hr F hF), norm_nonneg F]

end RhWeightedDilation
#print axioms RhWeightedDilation.dilatedPhysical_supported
#print axioms RhWeightedDilation.dilatedPhysical_energy_le
#print axioms RhWeightedDilation.outwardLift_physical_ae
#print axioms RhWeightedDilation.outwardLift_supported
#print axioms RhWeightedDilation.outwardLift_norm_le
