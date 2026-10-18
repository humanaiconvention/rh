import RhNativeCompleteDictionary001
import RhNativeBoundedPartControl001
import RhWeightedDilationInverse001

/-! Actual spatial translations preserve the COMPLETE weighted Fourier norm.
The native full-energy identity uses the L1/L2 Fourier phase theorem and AE
representatives, not an assumed isometry on an abstract form domain.
-/
set_option maxHeartbeats 100000
noncomputable section
open Set MeasureTheory Filter FourierTransform
open scoped Topology ENNReal
namespace RhWeightedTranslation
open RhWeightedMeasureEmbedding RhWeightedEnergyIdentity RhNativeCompleteBilinear
open RhNativeCompleteDictionary RhNativeBoundedPartControl

lemma physical_translation_as_toLp (u : WholeSpace) (a : ℝ) :
    translation a u = (RhDilation.translate_memLp (Lp.memLp u) a).toLp (fun t => u (t+a)) := by
  apply Lp.ext
  exact (translation_ae u a).trans
    (RhDilation.translate_memLp (Lp.memLp u) a).coeFn_toLp.symm

/-- Exact full multiplier energy under actual spatial translation. -/
theorem full_energy_translation (u : WholeSpace) (hu : Integrable u volume) (a b : ℝ) :
    RhTail.fullFrequencyEnergy b (translation a u) = RhTail.fullFrequencyEnergy b u := by
  rw [physical_translation_as_toLp]
  unfold RhTail.fullFrequencyEnergy
  apply lintegral_congr_ae
  have h := RhDilation.fourier_translate_L2_ae hu (Lp.memLp u) a
  rw [Lp.toLp_coeFn] at h
  filter_upwards [h] with xi hxi
  apply tsum_congr
  intro k
  simp only [RhTail.frequencySummand, RhTail.spectralDensity, hxi, norm_mul,
    Complex.norm_exp_ofReal_mul_I, one_mul]

/-- Constructed from the true translated spatial L2 class. -/
def translated (F : WeightedSpace) (hF : Integrable (physicalEmbedding F) volume)
    (a : ℝ) : WeightedSpace :=
  frequencyLift (translation a (physicalEmbedding F)) (by
    rw [full_energy_translation _ hF a (1/2)]
    exact weighted_native_energy_finite F)

lemma translated_physical (F : WeightedSpace) (hF : Integrable (physicalEmbedding F) volume)
    (a : ℝ) : physicalEmbedding (translated F hF a) = translation a (physicalEmbedding F) :=
  physicalEmbedding_frequencyLift _ _

lemma translated_physical_ae (F : WeightedSpace) (hF : Integrable (physicalEmbedding F) volume)
    (a : ℝ) : physicalEmbedding (translated F hF a) =ᵐ[volume]
      fun t => physicalEmbedding F (t+a) := by
  rw [translated_physical]
  exact translation_ae _ _

/-- No multiplier tail is omitted in this exact norm equality. -/
theorem translated_norm (F : WeightedSpace) (hF : Integrable (physicalEmbedding F) volume)
    (a : ℝ) : ‖translated F hF a‖ = ‖F‖ := by
  have hs : ‖translated F hF a‖ ^ 2 = ‖F‖ ^ 2 := by
    rw [translated, frequencyLift_norm_square,
      full_energy_translation _ hF a (1/2), translation_norm]
    exact (weighted_norm_square F).symm
  nlinarith [norm_nonneg (translated F hF a), norm_nonneg F]

end RhWeightedTranslation
#print axioms RhWeightedTranslation.full_energy_translation
#print axioms RhWeightedTranslation.translated_physical_ae
#print axioms RhWeightedTranslation.translated_norm
