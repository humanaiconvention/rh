import RhWeightedShiftBilinear001
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! Exact native weighted high-frequency mass estimate for actual physical
Fourier representatives. This proves no compactness or spectral gap by itself.
No logarithmic surrogate replaces the complete native multiplier. -/
set_option maxHeartbeats 0
noncomputable section
open Set MeasureTheory Filter FourierTransform
open scoped Topology ENNReal
namespace RhWeightedFrequencyTail
open RhWeightedMeasureEmbedding RhWeightedEnergyIdentity RhWeightedShiftBilinear

lemma weighted_square_integrable (F : WeightedSpace) :
    Integrable (fun xi => graphWeight xi * ‖F xi‖ ^ 2) volume := by
  have hi : Integrable (fun xi => ‖F xi‖ ^ 2) weightedMeasure :=
    (memLp_two_iff_integrable_sq_norm (Lp.memLp F).aestronglyMeasurable).mp (Lp.memLp F)
  have ht : ∀ᵐ xi ∂volume, archWeight xi < ⊤ :=
    Eventually.of_forall (fun xi => lt_top_iff_ne_top.mpr (archWeight_ne_top xi))
  have hh := (integrable_withDensity_iff_integrable_smul'
    archWeight_measurable ht).mp hi
  simpa only [smul_eq_mul, archWeight_real] using hh

lemma weighted_square_integral (F : WeightedSpace) :
    (∫ xi, graphWeight xi * ‖F xi‖ ^ 2) = ‖F‖ ^ 2 := by
  rw [lp_norm_sq_integral F]
  change _ = ∫ xi, ‖F xi‖ ^ 2 ∂volume.withDensity archWeight
  rw [integral_withDensity_eq_integral_toReal_smul archWeight_measurable
    (Eventually.of_forall (fun xi => lt_top_iff_ne_top.mpr (archWeight_ne_top xi)))]
  simp only [smul_eq_mul, archWeight_real]

lemma graphWeight_mono_outside {Omega xi : ℝ} (hOmega : 0 ≤ Omega)
    (hxi : Omega ≤ |xi|) : graphWeight Omega ≤ graphWeight xi := by
  have ha : |2 * Real.pi * Omega| ≤ |2 * Real.pi * xi| := by
    calc
      |2 * Real.pi * Omega| = |2 * Real.pi| * Omega := by
        simpa only [abs_of_nonneg hOmega] using abs_mul (2 * Real.pi) Omega
      _ ≤ |2 * Real.pi| * |xi| := mul_le_mul_of_nonneg_left hxi (abs_nonneg _)
      _ = |2 * Real.pi * xi| := (abs_mul _ _).symm
  exact add_le_add le_rfl
    (RhShiftFormMultiplier.archMultiplier_mono_abs (by norm_num) ha)

theorem raw_high_frequency_mass (F : WeightedSpace) {Omega : ℝ}
    (hOmega : 0 ≤ Omega) :
    (∫ xi in {xi : ℝ | Omega < |xi|}, ‖F xi‖ ^ 2) ≤
      ‖F‖ ^ 2 / graphWeight Omega := by
  let S : Set ℝ := {xi : ℝ | Omega < |xi|}
  have hS : MeasurableSet S := measurableSet_lt measurable_const continuous_abs.measurable
  have hF : MemLp (fun xi => F xi) 2 volume :=
    (Lp.memLp F).mono_measure volume_le_weightedMeasure
  have hmass : Integrable (fun xi => ‖F xi‖ ^ 2) volume :=
    (memLp_two_iff_integrable_sq_norm hF.aestronglyMeasurable).mp hF
  have hw := weighted_square_integrable F
  have hle : graphWeight Omega * (∫ xi in S, ‖F xi‖ ^ 2) ≤
      ∫ xi in S, graphWeight xi * ‖F xi‖ ^ 2 := by
    rw [← integral_const_mul]
    apply integral_mono_ae (hmass.integrableOn.const_mul _) hw.integrableOn
    filter_upwards [ae_restrict_mem hS] with xi hxi
    exact mul_le_mul_of_nonneg_right
      (graphWeight_mono_outside hOmega hxi.le) (sq_nonneg _)
  have htotal : (∫ xi in S, graphWeight xi * ‖F xi‖ ^ 2) ≤ ‖F‖ ^ 2 := by
    rw [← weighted_square_integral F]
    exact setIntegral_le_integral hw (Eventually.of_forall (fun xi =>
      mul_nonneg (graphWeight_positive xi).le (sq_nonneg _)))
  apply (le_div_iff₀ (graphWeight_positive Omega)).mpr
  simpa only [mul_comm] using hle.trans htotal

/-- Actual physical Fourier representatives and exact complete native
denominator. Support is unnecessary, so supported/core vectors inherit it. -/
theorem actual_high_frequency_mass (F : WeightedSpace) {Omega : ℝ}
    (hOmega : 0 ≤ Omega) :
    (∫ xi in {xi : ℝ | Omega < |xi|},
      ‖(𝓕 (physicalEmbedding F) : WholeSpace) xi‖ ^ 2) ≤
      ‖F‖ ^ 2 /
        (1 + RhDilationScalar.archMultiplier (1 / 2) (2 * Real.pi * Omega)) := by
  rw [physicalEmbedding_fourier]
  have he : (∫ xi in {xi : ℝ | Omega < |xi|}, ‖inclusion F xi‖ ^ 2) =
      ∫ xi in {xi : ℝ | Omega < |xi|}, ‖F xi‖ ^ 2 := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae (inclusion_ae F)] with xi hxi
    rw [hxi]
  rw [he]
  exact raw_high_frequency_mass F hOmega

end RhWeightedFrequencyTail
#print axioms RhWeightedFrequencyTail.weighted_square_integral
#print axioms RhWeightedFrequencyTail.raw_high_frequency_mass
#print axioms RhWeightedFrequencyTail.actual_high_frequency_mass
