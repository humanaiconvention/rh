import RhPrimitiveFormDomain001
import RhFourierCompatibility001
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence

/-!
A genuine complete-energy convergence lemma for the Fourier multipliers of
normalized compact smooth bumps. Spatial support-preserving approximation and
identification with Suzuki's closed form are not asserted in this module.
-/
noncomputable section
open MeasureTheory Filter FourierTransform
open scoped Topology ENNReal
namespace RhWeightedCoreAttempt

open RhTail

def bumpComplex (φ : ContDiffBump (0 : ℝ)) (x : ℝ) : ℂ :=
  (φ.normed volume x : ℂ)

lemma bumpComplex_integrable (φ : ContDiffBump (0 : ℝ)) :
    Integrable (bumpComplex φ) volume :=
  (φ.integrable_normed (μ := volume)).ofReal

lemma bump_fourier_continuous (φ : ContDiffBump (0 : ℝ)) :
    Continuous (𝓕 (bumpComplex φ)) :=
  RhTail.integral_fourier_continuous (bumpComplex_integrable φ)

lemma bump_fourier_zero (φ : ContDiffBump (0 : ℝ)) :
    (𝓕 (bumpComplex φ)) 0 = 1 := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  simp only [mul_zero, Complex.ofReal_zero, zero_mul, Complex.exp_zero, one_smul]
  unfold bumpComplex
  rw [integral_complex_ofReal, φ.integral_normed]
  norm_num

lemma bump_fourier_norm_le_one (φ : ContDiffBump (0 : ℝ)) (ξ : ℝ) :
    ‖(𝓕 (bumpComplex φ)) ξ‖ ≤ 1 := by
  have h := Real.norm_fourier_le_integral_norm (bumpComplex φ) ξ
  have he : (fun x => ‖bumpComplex φ x‖) = φ.normed volume := by
    funext x
    simp only [bumpComplex, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (φ.nonneg_normed x)]
  rw [he, φ.integral_normed] at h
  exact h

def bumpMultiplier (φ : ContDiffBump (0 : ℝ)) (n : ℕ) (ξ : ℝ) : ℂ :=
  (𝓕 (bumpComplex φ)) (ξ / ((n : ℝ) + 1))

lemma bumpMultiplier_continuous (φ : ContDiffBump (0 : ℝ)) (n : ℕ) :
    Continuous (bumpMultiplier φ n) :=
  (bump_fourier_continuous φ).comp (by fun_prop)

lemma bumpMultiplier_tendsto (φ : ContDiffBump (0 : ℝ)) (ξ : ℝ) :
    Tendsto (fun n => bumpMultiplier φ n ξ) atTop (𝓝 1) := by
  have hn : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    by
      simpa only [add_comm] using tendsto_atTop_add_const_left atTop (1 : ℝ)
        (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)
  have hi := tendsto_inv_atTop_zero.comp hn
  have hx : Tendsto (fun n : ℕ => ξ / ((n : ℝ) + 1)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, div_eq_mul_inv, mul_zero] using hi.const_mul ξ
  simpa only [Function.comp_def, bumpMultiplier, bump_fourier_zero] using
    (bump_fourier_continuous φ).continuousAt.tendsto.comp hx

def errorMultiplier (φ : ContDiffBump (0 : ℝ)) (n : ℕ) (ξ : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (‖bumpMultiplier φ n ξ - 1‖ ^ 2)

lemma errorMultiplier_aemeasurable (φ : ContDiffBump (0 : ℝ)) (n : ℕ) :
    AEMeasurable (errorMultiplier φ n) volume := by
  exact (((bumpMultiplier_continuous φ n).sub continuous_const).norm.pow 2).aemeasurable.ennreal_ofReal

lemma errorMultiplier_le_four (φ : ContDiffBump (0 : ℝ)) (n : ℕ) (ξ : ℝ) :
    errorMultiplier φ n ξ ≤ 4 := by
  have h : ‖bumpMultiplier φ n ξ - 1‖ ≤ ‖bumpMultiplier φ n ξ‖ + 1 := by
    simpa only [norm_one] using norm_sub_le (bumpMultiplier φ n ξ) (1 : ℂ)
  have hb := bump_fourier_norm_le_one φ (ξ / ((n : ℝ) + 1))
  change ‖bumpMultiplier φ n ξ‖ ≤ 1 at hb
  have hn : ‖bumpMultiplier φ n ξ - 1‖ ≤ 2 := by
    linarith
  have hs : ‖bumpMultiplier φ n ξ - 1‖ ^ 2 ≤ (4 : ℝ) := by
    nlinarith [norm_nonneg (bumpMultiplier φ n ξ - 1)]
  exact (ENNReal.ofReal_le_ofReal hs).trans_eq (by norm_num)

lemma errorMultiplier_tendsto_zero (φ : ContDiffBump (0 : ℝ)) (ξ : ℝ) :
    Tendsto (fun n => errorMultiplier φ n ξ) atTop (𝓝 0) := by
  have h := (((bumpMultiplier_tendsto φ ξ).sub_const 1).norm.pow 2)
  have hz : Tendsto (fun n => ‖bumpMultiplier φ n ξ - 1‖ ^ 2) atTop (𝓝 (0 : ℝ)) := by
    simpa using h
  simpa only [Function.comp_def, errorMultiplier, ENNReal.ofReal_zero] using
    (ENNReal.continuous_ofReal.tendsto 0).comp hz

/-- Complete weighted convergence; the integrable density is never truncated
or passed through a termwise triangle inequality. -/
theorem weighted_bump_error_tendsto_zero
    (φ : ContDiffBump (0 : ℝ)) (D : ℝ → ℝ≥0∞)
    (hD : AEMeasurable D volume) (hfin : (∫⁻ ξ, D ξ) ≠ ⊤) :
    Tendsto (fun n => ∫⁻ ξ, errorMultiplier φ n ξ * D ξ) atTop (𝓝 0) := by
  have hF : ∀ n, AEMeasurable (fun ξ => errorMultiplier φ n ξ * D ξ) volume :=
    fun n => (errorMultiplier_aemeasurable φ n).mul hD
  have hb : ∀ n, (fun ξ => errorMultiplier φ n ξ * D ξ) ≤ᵐ[volume]
      (fun ξ => 4 * D ξ) := by
    intro n
    exact Eventually.of_forall (fun ξ => mul_le_mul (errorMultiplier_le_four φ n ξ) le_rfl zero_le zero_le)
  have hf : (∫⁻ ξ, 4 * D ξ) ≠ ⊤ := by
    rw [lintegral_const_mul' _ _ (by norm_num : (4 : ℝ≥0∞) ≠ ⊤)]
    exact ENNReal.mul_ne_top (by norm_num) hfin
  have hl : ∀ᵐ ξ ∂volume, Tendsto
      (fun n => errorMultiplier φ n ξ * D ξ) atTop (𝓝 (0 : ℝ≥0∞)) := by
    filter_upwards [ae_lt_top' hD hfin] with ξ hξ
    simpa only [zero_mul] using
      ENNReal.Tendsto.mul_const (errorMultiplier_tendsto_zero φ ξ) (Or.inr hξ.ne)
  simpa only [lintegral_zero] using
    tendsto_lintegral_of_dominated_convergence' (fun ξ => 4 * D ξ) hF hb hf hl

def completeDensity (F : WholeSpace) (ξ : ℝ) : ℝ≥0∞ :=
  ∑' k : ℕ, frequencySummand (1 / 2) F k ξ

lemma completeDensity_aemeasurable (F : WholeSpace) :
    AEMeasurable (completeDensity F) volume :=
  AEMeasurable.tsum (fun k => frequencySummand_aemeasurable (by norm_num) F k)

/-- Every actual physical anchored primitive admits complete-energy convergence
of the normalized-bump Fourier multipliers, at every finite positive radius.
No smooth spatial core or Suzuki-domain closure is concluded here. -/
theorem physical_complete_bump_multiplier_convergence
    (φ : ContDiffBump (0 : ℝ)) {A : ℝ} (hA : 0 < A)
    {v : ℝ → ℝ} (hv : MemLp v 2 (RhAnchored.physicalMeasure A)) :
    Tendsto (fun n => ∫⁻ ξ, errorMultiplier φ n ξ * completeDensity
      (physicalFourierVector A (RhAnchored.primitive A v)
        (RhAnchored.primitive_memLp hv)) ξ) atTop (𝓝 0) := by
  apply weighted_bump_error_tendsto_zero φ _ (completeDensity_aemeasurable _)
  exact (RhPrimitiveFormDomain.physical_primitive_full_arch_finite hA hv).ne

end RhWeightedCoreAttempt
#print axioms RhWeightedCoreAttempt.bump_fourier_norm_le_one
#print axioms RhWeightedCoreAttempt.bumpMultiplier_tendsto
#print axioms RhWeightedCoreAttempt.weighted_bump_error_tendsto_zero
#print axioms RhWeightedCoreAttempt.physical_complete_bump_multiplier_convergence
