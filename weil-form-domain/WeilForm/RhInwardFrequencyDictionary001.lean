import RhWeightedFrequencyDilation001
import RhWeightedInwardMap001

/-! Exact match between whole weighted-frequency dilation and the existing
actual supported spatial inward map. The square-root Fourier Jacobian,
scaled null sets, and L2 representatives are all retained. -/
set_option maxHeartbeats 0
noncomputable section
open Set MeasureTheory Filter FourierTransform
open scoped Topology ENNReal
namespace RhInwardFrequencyDictionary
open RhDilation RhWeightedMeasureEmbedding RhWeightedEnergyIdentity
open RhWeightedDilation RhWeightedDilationInverse RhWeightedFrequencyDilation

/-- The actual spatial inward lift equals the WHOLE weighted-frequency rescale.
This permits frequency dense approximation without a false spatial support premise. -/
theorem inwardLift_eq_frequencyDilate {R r : ℝ} (hr : 1 ≤ r) (F : WeightedSpace)
    (hF : F ∈ supportedSubspace R) : inwardLift hr F hF = frequencyDilate hr F := by
  have hr0 : 0 < r := by linarith
  have hf := RhPhysicalShiftFourier.supported_integrable hF
  have hFourier : (𝓕 (physicalEmbedding F : ℝ → ℂ)) =ᵐ[volume] F := by
    have h := RhTail.integral_fourier_ae_L2 hf (Lp.memLp (physicalEmbedding F))
    rw [Lp.toLp_coeFn, physicalEmbedding_fourier] at h
    exact h.trans (inclusion_ae F)
  have hscaled := fourier_complexDilate_L2_ae (inv_pos.mpr hr0) hf
    (Lp.memLp (physicalEmbedding F))
  have hinc : inclusion (inwardLift hr F hF) =
      𝓕 (dilatedPhysical (inv_pos.mpr hr0) F hF) := by
    rw [← physicalEmbedding_fourier, inwardLift_physical]
  have hvol : (inwardLift hr F hF : ℝ → ℂ) =ᵐ[volume] complexDilate r F := by
    filter_upwards [(inclusion_ae (inwardLift hr F hF)).symm,
      hscaled, ae_comp_div hr0 hFourier] with xi hrep hsc hraw
    rw [hrep, hinc]
    change (𝓕 ((complexDilate_memLp (inv_pos.mpr hr0) hf
      (Lp.memLp (physicalEmbedding F))).toLp
        (complexDilate r⁻¹ (physicalEmbedding F))) : RhTail.WholeSpace) xi = _
    rw [hsc]
    have hx : r⁻¹ * xi = xi / r := by rw [div_eq_mul_inv, mul_comm]
    rw [hx, hraw, Real.sqrt_inv]
    rfl
  apply Lp.ext
  exact ((withDensity_absolutelyContinuous volume archWeight).ae_eq hvol).trans
    (frequencyDilate_ae hr F).symm

end RhInwardFrequencyDictionary
#print axioms RhInwardFrequencyDictionary.inwardLift_eq_frequencyDilate
