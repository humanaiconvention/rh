import RhWeightedDilation001
import RhDilationInverseEnergy001

/-! Actual inward transport with the exact native 5 log r budget. This is a
bounded inverse on the supported complete domain, not an assumed regularity
estimate or a residual sign assertion. -/
set_option maxHeartbeats 0
noncomputable section
open Set MeasureTheory Filter FourierTransform
open scoped Topology ENNReal
namespace RhWeightedDilationInverse
open RhDilation RhTail RhWeightedMeasureEmbedding RhWeightedEnergyIdentity
open RhWeightedDilation RhDilationInverseEnergy

lemma dilatedPhysical_inverse_energy_bound {R r : ℝ} (hr : 1 ≤ r) (F : WeightedSpace)
    (hF : F ∈ supportedSubspace R) :
    fullFrequencyEnergy (1 / 2)
      (dilatedPhysical (inv_pos.mpr (by linarith : 0 < r)) F hF) ≤
      fullFrequencyEnergy (1 / 2) (physicalEmbedding F) +
        ENNReal.ofReal ((5 * Real.log r) * ‖physicalEmbedding F‖ ^ 2) := by
  have hs := full_energy_inverse_bound hr (by norm_num : (0 : ℝ) < 1 / 2)
    (RhPhysicalShiftFourier.supported_integrable hF) (Lp.memLp (physicalEmbedding F))
  have hc : (1 : ℝ) + 2 / (1 / 2) = 5 := by norm_num
  simpa only [dilatedPhysical, Lp.toLp_coeFn, hc, ← lp_norm_sq_integral] using hs

lemma dilatedPhysical_inverse_energy_finite {R r : ℝ} (hr : 1 ≤ r) (F : WeightedSpace)
    (hF : F ∈ supportedSubspace R) :
    fullFrequencyEnergy (1 / 2)
      (dilatedPhysical (inv_pos.mpr (by linarith : 0 < r)) F hF) < ⊤ :=
  lt_of_le_of_lt (dilatedPhysical_inverse_energy_bound hr F hF)
    (ENNReal.add_lt_top.mpr ⟨weighted_native_energy_finite F, ENNReal.ofReal_lt_top⟩)

/-- Actual frequency lift of the inward spatial dilation. -/
def inwardLift {R r : ℝ} (hr : 1 ≤ r) (F : WeightedSpace)
    (hF : F ∈ supportedSubspace R) : WeightedSpace :=
  frequencyLift (dilatedPhysical (inv_pos.mpr (by linarith : 0 < r)) F hF)
    (dilatedPhysical_inverse_energy_finite hr F hF)

lemma inwardLift_physical {R r : ℝ} (hr : 1 ≤ r) (F : WeightedSpace)
    (hF : F ∈ supportedSubspace R) :
    physicalEmbedding (inwardLift hr F hF) =
      dilatedPhysical (inv_pos.mpr (by linarith : 0 < r)) F hF :=
  physicalEmbedding_frequencyLift _ _

lemma inwardLift_physical_ae {R r : ℝ} (hr : 1 ≤ r) (F : WeightedSpace)
    (hF : F ∈ supportedSubspace R) :
    physicalEmbedding (inwardLift hr F hF) =ᵐ[volume]
      complexDilate r⁻¹ (physicalEmbedding F) := by
  rw [inwardLift_physical]
  exact dilatedPhysical_ae _ F hF

lemma inwardLift_supported {R r : ℝ} (hr : 1 ≤ r) (F : WeightedSpace)
    (hF : F ∈ supportedSubspace R) :
    inwardLift hr F hF ∈ supportedSubspace (r⁻¹ * R) :=
  frequencyLift_mem_supportedSubspace (r⁻¹ * R) _ _
    (dilatedPhysical_supported (inv_pos.mpr (by linarith : 0 < r)) F hF)

/-- Exact bound in complete graph-norm square with the native logarithmic cost. -/
theorem inwardLift_norm_square_le {R r : ℝ} (hr : 1 ≤ r) (F : WeightedSpace)
    (hF : F ∈ supportedSubspace R) :
    ‖inwardLift hr F hF‖ ^ 2 ≤ (1 + 5 * Real.log r) * ‖F‖ ^ 2 := by
  have hbudget : 0 ≤ (5 * Real.log r) * ‖physicalEmbedding F‖ ^ 2 :=
    mul_nonneg (mul_nonneg (by norm_num) (Real.log_nonneg hr)) (sq_nonneg _)
  have hE := ENNReal.toReal_mono
    (ENNReal.add_ne_top.mpr ⟨(weighted_native_energy_finite F).ne, ENNReal.ofReal_ne_top⟩)
    (dilatedPhysical_inverse_energy_bound hr F hF)
  rw [ENNReal.toReal_add (weighted_native_energy_finite F).ne ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hbudget] at hE
  have hM : ‖physicalEmbedding F‖ ^ 2 ≤ ‖F‖ ^ 2 := by
    rw [weighted_norm_square F]
    exact le_add_of_nonneg_right ENNReal.toReal_nonneg
  have hN := weighted_norm_square F
  rw [inwardLift, frequencyLift_norm_square, dilatedPhysical_norm_square]
  nlinarith [mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 5) (Real.log_nonneg hr)) (sub_nonneg.mpr hM)]

lemma inwardLift_norm_le {R r : ℝ} (hr : 1 ≤ r) (F : WeightedSpace)
    (hF : F ∈ supportedSubspace R) :
    ‖inwardLift hr F hF‖ ≤ Real.sqrt (1 + 5 * Real.log r) * ‖F‖ := by
  have hl : 0 ≤ Real.log r := Real.log_nonneg hr
  have hc : 0 ≤ 1 + 5 * Real.log r := by linarith
  have hsq := Real.sq_sqrt hc
  have hn := inwardLift_norm_square_le hr F hF
  have hs : 0 ≤ Real.sqrt (1 + 5 * Real.log r) := Real.sqrt_nonneg _
  have hp : (Real.sqrt (1 + 5 * Real.log r) * ‖F‖) ^ 2 =
      (1 + 5 * Real.log r) * ‖F‖ ^ 2 := by rw [mul_pow, hsq]
  have hpn : 0 ≤ Real.sqrt (1 + 5 * Real.log r) * ‖F‖ := mul_nonneg hs (norm_nonneg F)
  nlinarith [norm_nonneg (inwardLift hr F hF)]

lemma complexDilate_congr_ae {r : ℝ} (hr : 0 < r) {f g : ℝ → ℂ}
    (h : f =ᵐ[volume] g) : complexDilate r f =ᵐ[volume] complexDilate r g := by
  filter_upwards [ae_comp_div hr h] with t ht
  simp only [complexDilate, ht]

/-- The inward and outward lifts are actual inverses on their native supports. -/
theorem inward_outward_cancel {R r : ℝ} (hr : 1 ≤ r) (F : WeightedSpace)
    (hF : F ∈ supportedSubspace R) :
    inwardLift hr (outwardLift hr F hF) (outwardLift_supported hr F hF) = F := by
  apply physicalEmbedding_injective
  apply Lp.ext
  have h := (inwardLift_physical_ae hr (outwardLift hr F hF)
    (outwardLift_supported hr F hF)).trans
      (complexDilate_congr_ae (inv_pos.mpr (by linarith : 0 < r))
        (outwardLift_physical_ae hr F hF))
  rw [complexDilate_inverse_cancel_left (by linarith : 0 < r)] at h
  exact h

theorem outward_inward_cancel {R r : ℝ} (hr : 1 ≤ r) (F : WeightedSpace)
    (hF : F ∈ supportedSubspace R) :
    outwardLift hr (inwardLift hr F hF) (inwardLift_supported hr F hF) = F := by
  apply physicalEmbedding_injective
  apply Lp.ext
  have h := (outwardLift_physical_ae hr (inwardLift hr F hF)
    (inwardLift_supported hr F hF)).trans
      (complexDilate_congr_ae (by linarith : 0 < r)
        (inwardLift_physical_ae hr F hF))
  rw [complexDilate_inverse_cancel (by linarith : 0 < r)] at h
  exact h

end RhWeightedDilationInverse
#print axioms RhWeightedDilationInverse.dilatedPhysical_inverse_energy_bound
#print axioms RhWeightedDilationInverse.inwardLift_physical_ae
#print axioms RhWeightedDilationInverse.inwardLift_supported
#print axioms RhWeightedDilationInverse.inwardLift_norm_square_le
#print axioms RhWeightedDilationInverse.inward_outward_cancel
#print axioms RhWeightedDilationInverse.outward_inward_cancel
