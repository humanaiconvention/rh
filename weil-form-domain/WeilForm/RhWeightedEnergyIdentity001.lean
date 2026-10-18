import RhWeightedMeasureEmbedding001
import RhFourierMonotone001

/-!
Exact weighted norm/energy dictionary and genuine lifting of finite-energy
spatial L2 vectors. All infinite quantities are first handled in ENNReal;
conversion to real numbers follows proved finiteness. No arithmetic sign,
closed-form positivity, or smooth-core hypothesis is introduced.
-/
set_option maxHeartbeats 0
noncomputable section
open Set MeasureTheory Filter FourierTransform
open scoped Topology BigOperators ENNReal
namespace RhWeightedEnergyIdentity
open RhWeightedMeasureEmbedding

/-- Complete positive frequency energy of an actual representative. -/
def frequencyEnergy (f : ℝ → ℂ) : ℝ≥0∞ :=
  ∫⁻ xi, ∑' k : ℕ, archSummand k xi * ENNReal.ofReal (‖f xi‖ ^ 2)

lemma frequencyEnergy_congr_ae {f g : ℝ → ℂ} (h : f =ᵐ[volume] g) :
    frequencyEnergy f = frequencyEnergy g := by
  apply lintegral_congr_ae
  filter_upwards [h] with xi hxi
  rw [hxi]

/-- Exact native summands, including the actual angular-frequency normalization. -/
theorem native_energy_as_frequency (u : WholeSpace) :
    RhTail.fullFrequencyEnergy (1 / 2) u = frequencyEnergy (fun xi => (𝓕 u : WholeSpace) xi) := by
  unfold RhTail.fullFrequencyEnergy frequencyEnergy
  apply lintegral_congr
  intro xi
  apply tsum_congr
  intro k
  unfold RhTail.frequencySummand RhTail.spectralDensity archSummand RhTail.angularSquare
  rw [ENNReal.ofReal_mul (RhTail.multiplier_nonneg (sq_nonneg _) (by positivity))]

lemma lp_norm_sq_integral {mu : Measure ℝ} (F : Lp (α := ℝ) ℂ 2 mu) :
    ‖F‖ ^ 2 = ∫ xi, ‖F xi‖ ^ 2 ∂mu := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  exact Eventually.of_forall (fun xi => real_inner_self_eq_norm_sq (F xi))

lemma lp_lintegral_norm_sq {mu : Measure ℝ} (F : Lp (α := ℝ) ℂ 2 mu) :
    (∫⁻ xi, ENNReal.ofReal (‖F xi‖ ^ 2) ∂mu) = ENNReal.ofReal (‖F‖ ^ 2) := by
  have hi := (memLp_two_iff_integrable_sq_norm (Lp.memLp F).aestronglyMeasurable).mp (Lp.memLp F)
  rw [← ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall (fun _ => sq_nonneg _)),
    ← lp_norm_sq_integral F]

/-- Weighted measure decomposes into physical mass and complete nonnegative energy. -/
theorem weighted_square_integral_split (f : ℝ → ℂ) (hf : Measurable f) :
    (∫⁻ xi, ENNReal.ofReal (‖f xi‖ ^ 2) ∂weightedMeasure) =
      (∫⁻ xi, ENNReal.ofReal (‖f xi‖ ^ 2) ∂volume) + frequencyEnergy f := by
  have hsq : Measurable (fun xi => ENNReal.ofReal (‖f xi‖ ^ 2)) :=
    (hf.norm.pow_const 2).ennreal_ofReal
  unfold weightedMeasure
  rw [lintegral_withDensity_eq_lintegral_mul volume archWeight_measurable hsq]
  calc
    (∫⁻ xi, (archWeight * (fun xi => ENNReal.ofReal (‖f xi‖ ^ 2))) xi) =
        ∫⁻ xi, ENNReal.ofReal (‖f xi‖ ^ 2) +
          ∑' k : ℕ, archSummand k xi * ENNReal.ofReal (‖f xi‖ ^ 2) := by
      apply lintegral_congr
      intro xi
      simp only [Pi.mul_apply, archWeight, add_mul, one_mul, ENNReal.tsum_mul_right]
    _ = (∫⁻ xi, ENNReal.ofReal (‖f xi‖ ^ 2)) + frequencyEnergy f :=
      lintegral_add_left hsq _

lemma physicalEmbedding_fourier (F : WeightedSpace) :
    𝓕 (physicalEmbedding F) = inclusion F := by
  change (Lp.fourierTransformₗᵢ ℝ ℂ)
    ((Lp.fourierTransformₗᵢ ℝ ℂ).symm (inclusion F)) = inclusion F
  exact (Lp.fourierTransformₗᵢ ℝ ℂ).apply_symm_apply (inclusion F)

lemma norm_physicalEmbedding (F : WeightedSpace) : ‖physicalEmbedding F‖ = ‖inclusion F‖ := by
  change ‖(Lp.fourierTransformₗᵢ ℝ ℂ).symm (inclusion F)‖ = ‖inclusion F‖
  exact (Lp.fourierTransformₗᵢ ℝ ℂ).symm.norm_map (inclusion F)

/-- Genuine graph-norm equality before any finite-energy conversion to real values. -/
theorem weighted_norm_square_ennreal (F : WeightedSpace) :
    ENNReal.ofReal (‖F‖ ^ 2) = ENNReal.ofReal (‖physicalEmbedding F‖ ^ 2) +
      RhTail.fullFrequencyEnergy (1 / 2) (physicalEmbedding F) := by
  have hs := weighted_square_integral_split F (Lp.stronglyMeasurable F).measurable
  have hmass : (∫⁻ xi, ENNReal.ofReal (‖F xi‖ ^ 2)) =
      ENNReal.ofReal (‖physicalEmbedding F‖ ^ 2) := by
    calc
      _ = ∫⁻ xi, ENNReal.ofReal (‖inclusion F xi‖ ^ 2) := by
        apply lintegral_congr_ae
        filter_upwards [inclusion_ae F] with xi hxi
        rw [hxi]
      _ = ENNReal.ofReal (‖inclusion F‖ ^ 2) := lp_lintegral_norm_sq (inclusion F)
      _ = ENNReal.ofReal (‖physicalEmbedding F‖ ^ 2) := by rw [norm_physicalEmbedding]
  have henergy : frequencyEnergy F = RhTail.fullFrequencyEnergy (1 / 2) (physicalEmbedding F) := by
    rw [native_energy_as_frequency, physicalEmbedding_fourier]
    exact frequencyEnergy_congr_ae (inclusion_ae F).symm
  rw [lp_lintegral_norm_sq F, hmass, henergy] at hs
  exact hs

/-- Every vector of the actual weighted space has finite native complete energy. -/
theorem weighted_native_energy_finite (F : WeightedSpace) :
    RhTail.fullFrequencyEnergy (1 / 2) (physicalEmbedding F) < ⊤ := by
  have hle : RhTail.fullFrequencyEnergy (1 / 2) (physicalEmbedding F) ≤
      ENNReal.ofReal (‖F‖ ^ 2) := by
    rw [weighted_norm_square_ennreal]
    exact le_add_of_nonneg_left (by positivity)
  exact lt_of_le_of_lt hle ENNReal.ofReal_lt_top

/-- Exact real graph-norm identity, with finiteness proved rather than assumed. -/
theorem weighted_norm_square (F : WeightedSpace) :
    ‖F‖ ^ 2 = ‖physicalEmbedding F‖ ^ 2 +
      (RhTail.fullFrequencyEnergy (1 / 2) (physicalEmbedding F)).toReal := by
  have h := congrArg ENNReal.toReal (weighted_norm_square_ennreal F)
  rw [ENNReal.toReal_add ENNReal.ofReal_ne_top (weighted_native_energy_finite F).ne,
    ENNReal.toReal_ofReal (sq_nonneg ‖F‖),
    ENNReal.toReal_ofReal (sq_nonneg ‖physicalEmbedding F‖)] at h
  exact h

/-- Finite native energy puts the actual L2 Fourier representative in weighted L2. -/
theorem fourier_memLp_weighted (u : WholeSpace)
    (hu : RhTail.fullFrequencyEnergy (1 / 2) u < ⊤) :
    MemLp (fun xi => (𝓕 u) xi) 2 weightedMeasure := by
  have hm : Measurable (fun xi => (𝓕 u) xi) := (Lp.stronglyMeasurable (𝓕 u)).measurable
  have hs := weighted_square_integral_split (fun xi => (𝓕 u : WholeSpace) xi) hm
  rw [lp_lintegral_norm_sq (𝓕 u), ← native_energy_as_frequency u] at hs
  have hfinite : (∫⁻ xi, ENNReal.ofReal (‖(𝓕 u) xi‖ ^ 2) ∂weightedMeasure) < ⊤ := by
    rw [hs]
    exact ENNReal.add_lt_top.mpr ⟨ENNReal.ofReal_lt_top, hu⟩
  apply (memLp_two_iff_integrable_sq_norm
    (Lp.stronglyMeasurable (𝓕 u)).aestronglyMeasurable).mpr
  refine ⟨(hm.norm.pow_const 2).aestronglyMeasurable, ?_⟩
  exact (hasFiniteIntegral_iff_ofReal (Eventually.of_forall (fun _ => sq_nonneg _))).mpr hfinite

/-- An actual lift, formed using the proved weighted MemLp statement. -/
def frequencyLift (u : WholeSpace) (hu : RhTail.fullFrequencyEnergy (1 / 2) u < ⊤) : WeightedSpace :=
  (fourier_memLp_weighted u hu).toLp (fun xi => (𝓕 u) xi)

lemma inclusion_frequencyLift (u : WholeSpace) (hu : RhTail.fullFrequencyEnergy (1 / 2) u < ⊤) :
    inclusion (frequencyLift u hu) = 𝓕 u := by
  apply Lp.ext
  have he := (fourier_memLp_weighted u hu).coeFn_toLp
  have hle := Measure.absolutelyContinuous_of_le volume_le_weightedMeasure
  exact (inclusion_ae (frequencyLift u hu)).trans (hle.ae_eq he)

/-- The lift reconstructs the original spatial L2 class exactly. -/
theorem physicalEmbedding_frequencyLift (u : WholeSpace)
    (hu : RhTail.fullFrequencyEnergy (1 / 2) u < ⊤) :
    physicalEmbedding (frequencyLift u hu) = u := by
  change (Lp.fourierTransformₗᵢ ℝ ℂ).symm (inclusion (frequencyLift u hu)) = u
  rw [inclusion_frequencyLift]
  exact (Lp.fourierTransformₗᵢ ℝ ℂ).symm_apply_apply u

/-- The lifted norm is the exact mass plus full native energy of the given vector. -/
theorem frequencyLift_norm_square (u : WholeSpace)
    (hu : RhTail.fullFrequencyEnergy (1 / 2) u < ⊤) :
    ‖frequencyLift u hu‖ ^ 2 = ‖u‖ ^ 2 + (RhTail.fullFrequencyEnergy (1 / 2) u).toReal := by
  simpa only [physicalEmbedding_frequencyLift] using weighted_norm_square (frequencyLift u hu)

/-- Actual support survives the weighted lift, as an AE statement. -/
theorem frequencyLift_mem_supportedSubspace (R : ℝ) (u : WholeSpace)
    (hu : RhTail.fullFrequencyEnergy (1 / 2) u < ⊤)
    (hs : ∀ᵐ t ∂volume, t ∉ Icc (-R) R → u t = 0) :
    frequencyLift u hu ∈ supportedSubspace R := by
  rw [mem_supportedSubspace_iff, physicalEmbedding_frequencyLift]
  exact hs

end RhWeightedEnergyIdentity
#print axioms RhWeightedEnergyIdentity.native_energy_as_frequency
#print axioms RhWeightedEnergyIdentity.weighted_square_integral_split
#print axioms RhWeightedEnergyIdentity.weighted_norm_square_ennreal
#print axioms RhWeightedEnergyIdentity.weighted_native_energy_finite
#print axioms RhWeightedEnergyIdentity.weighted_norm_square
#print axioms RhWeightedEnergyIdentity.fourier_memLp_weighted
#print axioms RhWeightedEnergyIdentity.physicalEmbedding_frequencyLift
#print axioms RhWeightedEnergyIdentity.frequencyLift_norm_square
#print axioms RhWeightedEnergyIdentity.frequencyLift_mem_supportedSubspace
