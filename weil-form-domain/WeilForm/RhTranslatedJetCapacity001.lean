import RhWeightedTranslation001
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! Actual translated inward-capacity vectors in the COMPLETE weighted norm.
Every Fourier mode is retained. Jet evaluation identities for a proposed
point-supported functional are explicit hypotheses; norm convergence is not.
-/
set_option maxHeartbeats 100000
noncomputable section
open Set MeasureTheory Filter FourierTransform
open scoped Topology ENNReal
namespace RhTranslatedJetCapacity
open RhWeightedMeasureEmbedding RhWeightedEnergyIdentity RhWeightedDilationInverse
open RhWeightedTranslation

def scale (n : ℕ) : ℝ := (n : ℝ) + 1
lemma scale_ge_one (n : ℕ) : 1 ≤ scale n := by
  unfold scale
  have h : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  linarith
lemma scale_pos (n : ℕ) : 0 < scale n := lt_of_lt_of_le zero_lt_one (scale_ge_one n)

def jetScalar (j n : ℕ) : ℝ := (scale n ^ j)⁻¹ * (Real.sqrt (scale n))⁻¹

def translatedInward {R : ℝ} (F : WeightedSpace) (hF : F ∈ supportedSubspace R)
    (x : ℝ) (n : ℕ) : WeightedSpace :=
  translated (inwardLift (scale_ge_one n) F hF)
    (RhPhysicalShiftFourier.supported_integrable (inwardLift_supported (scale_ge_one n) F hF)) (-x)

def jetVector {R : ℝ} (j : ℕ) (F : WeightedSpace) (hF : F ∈ supportedSubspace R)
    (x : ℝ) (n : ℕ) : WeightedSpace := jetScalar j n • translatedInward F hF x n

lemma jetScalar_square (j n : ℕ) :
    (jetScalar j n) ^ 2 = ((scale n ^ j)⁻¹) ^ 2 / scale n := by
  unfold jetScalar
  simp only [mul_pow, inv_pow, Real.sq_sqrt (scale_pos n).le, div_eq_mul_inv]

/-- Exact quantitative capacity bound at every finite scaling parameter. -/
theorem jetVector_norm_square_le {R : ℝ} (j : ℕ) (F : WeightedSpace)
    (hF : F ∈ supportedSubspace R) (x : ℝ) (n : ℕ) :
    ‖jetVector j F hF x n‖ ^ 2 ≤
      (((scale n ^ j)⁻¹) ^ 2 / scale n) * (1 + 5 * Real.log (scale n)) * ‖F‖ ^ 2 := by
  rw [jetVector, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
    jetScalar_square, translatedInward, translated_norm]
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
    (inwardLift_norm_square_le (scale_ge_one n) F hF)
    (div_nonneg (sq_nonneg ((scale n ^ j)⁻¹)) (scale_pos n).le)

/-- A single j-independent upper bound suffices for all nonnegative jets. -/
lemma jetVector_uniform_square_le {R : ℝ} (j : ℕ) (F : WeightedSpace)
    (hF : F ∈ supportedSubspace R) (x : ℝ) (n : ℕ) :
    ‖jetVector j F hF x n‖ ^ 2 ≤
      ((1 + 5 * Real.log (scale n)) / scale n) * ‖F‖ ^ 2 := by
  have hp : 1 ≤ scale n ^ j := one_le_pow₀ (scale_ge_one n)
  have hi : 0 ≤ (scale n ^ j)⁻¹ := inv_nonneg.mpr (by positivity)
  have hi1 : (scale n ^ j)⁻¹ ≤ 1 := (inv_le_one₀ (by positivity)).mpr hp
  have hisq : ((scale n ^ j)⁻¹)^2 ≤ 1 := by nlinarith
  have hc : 0 ≤ 1 + 5 * Real.log (scale n) := by
    have hh := Real.log_nonneg (scale_ge_one n)
    linarith
  apply (jetVector_norm_square_le j F hF x n).trans
  have hm := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right ((div_le_div_iff_of_pos_right (scale_pos n)).mpr hisq) hc)
    (sq_nonneg ‖F‖)
  convert hm using 1 <;> ring

lemma logarithmic_capacity_tendsto :
    Tendsto (fun n => (1 + 5 * Real.log (scale n)) / scale n) atTop (𝓝 (0 : ℝ)) := by
  have hs : Tendsto scale atTop atTop := by
    change Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop
    exact tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hi : Tendsto (fun y : ℝ => 1 / y) atTop (𝓝 (0 : ℝ)) := by
    simpa only [one_div] using (tendsto_inv_atTop_zero : Tendsto (fun y : ℝ => y⁻¹) atTop (𝓝 0))
  have hl : Tendsto (fun y : ℝ => Real.log y / y) atTop (𝓝 (0 : ℝ)) := by
    simpa only [pow_one, one_mul, add_zero] using
      Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  have hh := hi.add (hl.const_mul 5)
  have ht : Tendsto (fun y : ℝ => (1 + 5 * Real.log y) / y) atTop (𝓝 (0 : ℝ)) := by
    simpa only [add_div, mul_div_assoc, mul_zero, add_zero] using hh
  exact ht.comp hs

/-- Actual translated graph-norm convergence. No regularity assumption on
F beyond its actual supported weighted membership is needed. -/
theorem jetVector_norm_tendsto_zero {R : ℝ} (j : ℕ) (F : WeightedSpace)
    (hF : F ∈ supportedSubspace R) (x : ℝ) :
    Tendsto (fun n => ‖jetVector j F hF x n‖) atTop (𝓝 0) := by
  have hsq : Tendsto (fun n => ‖jetVector j F hF x n‖ ^ 2) atTop (𝓝 (0 : ℝ)) := by
    have hu := logarithmic_capacity_tendsto.mul_const (‖F‖ ^ 2)
    have hu0 : Tendsto (fun n => ((1 + 5 * Real.log (scale n)) / scale n) * ‖F‖ ^ 2)
        atTop (𝓝 (0 : ℝ)) := by simpa only [zero_mul] using hu
    exact squeeze_zero (fun n => sq_nonneg _) (jetVector_uniform_square_le j F hF x) hu0
  have h := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using h

/-- Once exact jet evaluation on the ACTUAL scaled test vectors is supplied,
a continuous complete-form functional cannot retain a nonzero point jet. -/
theorem continuous_functional_constant_jet_zero {R : ℝ} (j : ℕ) (F : WeightedSpace)
    (hF : F ∈ supportedSubspace R) (x : ℝ) (T : WeightedSpace →L[ℝ] ℝ) {a : ℝ}
    (hjet : ∀ᶠ n in atTop, T (jetVector j F hF x n) = a) : a = 0 := by
  have hz : Tendsto (jetVector j F hF x) atTop (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr (jetVector_norm_tendsto_zero j F hF x)
  have hT : Tendsto (fun n => T (jetVector j F hF x n)) atTop (𝓝 (0 : ℝ)) := by
    simpa only [Function.comp_def, map_zero] using T.continuous.continuousAt.tendsto.comp hz
  have ha : Tendsto (fun _ : ℕ => a) atTop (𝓝 (0 : ℝ)) := hT.congr' hjet
  exact tendsto_nhds_unique tendsto_const_nhds ha

end RhTranslatedJetCapacity
#print axioms RhTranslatedJetCapacity.jetVector_norm_square_le
#print axioms RhTranslatedJetCapacity.jetVector_norm_tendsto_zero
#print axioms RhTranslatedJetCapacity.continuous_functional_constant_jet_zero
