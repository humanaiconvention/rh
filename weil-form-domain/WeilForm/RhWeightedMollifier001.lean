import RhWeightedEnergyIdentity001
import RhWeightedCoreAttempt001

/-! Actual normalized-mollifier multiplication in the COMPLETE weighted Fourier
Hilbert space. The norm limit is proved by one dominated nonnegative integral;
there is no truncation of the native graph weight. Spatial convolution and
support identification are separate from this module. -/
noncomputable section
open MeasureTheory Filter FourierTransform
open scoped Topology ENNReal
namespace RhWeightedMollifier
open RhWeightedMeasureEmbedding RhWeightedEnergyIdentity RhWeightedCoreAttempt

lemma mollified_memLp (phi : ContDiffBump (0 : ℝ)) (n : ℕ) (F : WeightedSpace) :
    MemLp (fun xi => bumpMultiplier phi n xi * F xi) 2 weightedMeasure := by
  apply (Lp.memLp F).mono
  · exact (bumpMultiplier_continuous phi n).aestronglyMeasurable.mul
      (Lp.memLp F).aestronglyMeasurable
  · exact Eventually.of_forall (fun xi => by
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_right
        (bump_fourier_norm_le_one phi (xi / ((n : ℝ) + 1)))
        (norm_nonneg (F xi))).trans_eq (one_mul _))

def mollified (phi : ContDiffBump (0 : ℝ)) (n : ℕ) (F : WeightedSpace) : WeightedSpace :=
  (mollified_memLp phi n F).toLp (fun xi => bumpMultiplier phi n xi * F xi)

lemma mollified_ae (phi : ContDiffBump (0 : ℝ)) (n : ℕ) (F : WeightedSpace) :
    (mollified phi n F : ℝ → ℂ) =ᵐ[weightedMeasure]
      fun xi => bumpMultiplier phi n xi * F xi :=
  (mollified_memLp phi n F).coeFn_toLp

/-- Full graph density of an actual weighted L2 representative. -/
def density (F : WeightedSpace) (xi : ℝ) : ℝ≥0∞ :=
  archWeight xi * ENNReal.ofReal (‖F xi‖ ^ 2)

lemma density_measurable (F : WeightedSpace) : Measurable (density F) :=
  archWeight_measurable.mul
    (((Lp.stronglyMeasurable F).measurable.norm.pow_const 2).ennreal_ofReal)

lemma density_integral (F : WeightedSpace) :
    (∫⁻ xi, density F xi) = ENNReal.ofReal (‖F‖ ^ 2) := by
  have hsq : Measurable (fun xi => ENNReal.ofReal (‖F xi‖ ^ 2)) :=
    ((Lp.stronglyMeasurable F).measurable.norm.pow_const 2).ennreal_ofReal
  rw [← lp_lintegral_norm_sq F]
  exact (lintegral_withDensity_eq_lintegral_mul volume archWeight_measurable hsq).symm

/-- Literal weighted quotient error, including both ordinary mass and all native
frequencies. No energy convergence is imposed as a premise. -/
theorem error_norm_square (phi : ContDiffBump (0 : ℝ)) (n : ℕ) (F : WeightedSpace) :
    ENNReal.ofReal (‖mollified phi n F - F‖ ^ 2) =
      ∫⁻ xi, errorMultiplier phi n xi * density F xi := by
  rw [← lp_lintegral_norm_sq]
  have hsq : Measurable (fun xi => ENNReal.ofReal
      (‖(bumpMultiplier phi n xi - 1) * F xi‖ ^ 2)) := by
    exact (((bumpMultiplier_continuous phi n).measurable.sub measurable_const).mul
      (Lp.stronglyMeasurable F).measurable).norm.pow_const 2 |>.ennreal_ofReal
  calc
    (∫⁻ xi, ENNReal.ofReal (‖(mollified phi n F - F) xi‖ ^ 2) ∂weightedMeasure) =
        ∫⁻ xi, ENNReal.ofReal (‖(bumpMultiplier phi n xi - 1) * F xi‖ ^ 2)
          ∂weightedMeasure := by
      apply lintegral_congr_ae
      filter_upwards [Lp.coeFn_sub (mollified phi n F) F, mollified_ae phi n F]
        with xi hsub hm
      rw [hsub, Pi.sub_apply, hm]
      congr 2
      ring
    _ = ∫⁻ xi, archWeight xi * ENNReal.ofReal
        (‖(bumpMultiplier phi n xi - 1) * F xi‖ ^ 2) :=
      lintegral_withDensity_eq_lintegral_mul volume archWeight_measurable hsq
    _ = _ := by
      apply lintegral_congr
      intro xi
      rw [norm_mul, mul_pow, ENNReal.ofReal_mul (sq_nonneg _)]
      unfold errorMultiplier density
      ring

/-- Complete weighted Fourier mollifier convergence for EVERY weighted vector. -/
theorem mollified_norm_tendsto (phi : ContDiffBump (0 : ℝ)) (F : WeightedSpace) :
    Tendsto (fun n => ‖mollified phi n F - F‖) atTop (𝓝 0) := by
  have h := weighted_bump_error_tendsto_zero phi (density F)
    (density_measurable F).aemeasurable (by rw [density_integral]; exact ENNReal.ofReal_ne_top)
  have he : Tendsto (fun n => ENNReal.ofReal (‖mollified phi n F - F‖ ^ 2))
      atTop (𝓝 0) := by simpa only [error_norm_square] using h
  have hr : Tendsto (fun n => ‖mollified phi n F - F‖ ^ 2) atTop (𝓝 0) := by
    have ht := (ENNReal.continuousAt_toReal (by norm_num : (0 : ℝ≥0∞) ≠ ⊤)).tendsto.comp he
    simpa only [Function.comp_def, ENNReal.toReal_ofReal (sq_nonneg _),
      ENNReal.toReal_zero] using ht
  have hs := Real.continuous_sqrt.continuousAt.tendsto.comp hr
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using hs

end RhWeightedMollifier
#print axioms RhWeightedMollifier.density_integral
#print axioms RhWeightedMollifier.error_norm_square
#print axioms RhWeightedMollifier.mollified_norm_tendsto
