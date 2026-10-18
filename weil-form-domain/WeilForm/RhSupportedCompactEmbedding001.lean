import RhFourierGridOperator001
import RhFourierGridGlobalError001

/-! Actual compactness of the full complete supported-domain embedding.
Only norm approximation by explicit finite Fourier grids is used. -/
set_option maxHeartbeats 0
noncomputable section
open Set MeasureTheory Filter FourierTransform
open scoped Topology BigOperators
namespace RhSupportedCompactEmbedding
open RhWeightedMeasureEmbedding RhWeightedEnergyIdentity RhWeightedShiftBilinear
open RhSupportedMollifier RhFourierGridOperator RhFourierGridGlobalError

def frequencyEmbedding (R : ℝ) : SupportedSpace R →L[ℝ] WholeSpace :=
  inclusion.comp (supportedSubspace R).subtypeL

lemma grid_error_norm_square {R : ℝ} (F : SupportedSpace R) (Omega : ℝ) (M : ℕ) :
    ‖frequencyEmbedding R F - grid R Omega M F‖ ^ 2 =
      ∫ xi, ‖(𝓕 (representative R F)) xi -
        RhFiniteFourierGrid.step Omega M (𝓕 (representative R F)) xi‖ ^ 2 := by
  rw [lp_norm_sq_integral]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub (frequencyEmbedding R F) (grid R Omega M F),
    inclusion_ae (F : WeightedSpace), grid_ae F Omega M, raw_fourier_ae F]
    with xi hs hi hg hf
  dsimp only [Pi.sub_apply] at hs
  change (frequencyEmbedding R F : ℝ → ℂ) xi = _ at hi
  rw [hs, hi, hg, hf]

lemma grid_error_bound {R Omega : ℝ} (hR : 0 < R) (hO : 0 < Omega)
    {M : ℕ} (hM : 0 < M) (F : SupportedSpace R) :
    ‖frequencyEmbedding R F - grid R Omega M F‖ ^ 2 ≤
      (1 / graphWeight Omega + 64 * Real.pi ^ 2 * R ^ 3 * Omega ^ 3 / M ^ 2) * ‖F‖ ^ 2 := by
  rw [grid_error_norm_square]
  exact full_grid_error hR hO hM F

def band (n : ℕ) : ℝ := (n : ℝ) + 1
def count (n : ℕ) : ℕ := (n + 1)^2

def budget (R : ℝ) (n : ℕ) : ℝ :=
  1 / graphWeight (band n) + (64 * Real.pi ^ 2 * R ^ 3) / band n

lemma band_pos (n : ℕ) : 0 < band n := by unfold band; positivity
lemma count_pos (n : ℕ) : 0 < count n := by unfold count; positivity
lemma budget_nonneg {R : ℝ} (hR : 0 < R) (n : ℕ) : 0 ≤ budget R n := by
  unfold budget
  exact add_nonneg (div_nonneg (by norm_num) (graphWeight_positive _).le)
    (div_nonneg (by positivity) (band_pos n).le)

lemma budget_eq (R : ℝ) (n : ℕ) :
    (1 / graphWeight (band n) +
      64 * Real.pi ^ 2 * R ^ 3 * band n ^ 3 / (count n : ℝ) ^ 2) = budget R n := by
  unfold budget count band
  simp only [Nat.cast_pow, Nat.cast_add, Nat.cast_one]
  have hn : (n : ℝ) + 1 ≠ 0 := ne_of_gt (by positivity)
  field_simp


lemma band_atTop : Tendsto band atTop atTop :=
  tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop

lemma budget_tendsto_zero (R : ℝ) : Tendsto (budget R) atTop (𝓝 0) := by
  have ha : Tendsto (fun n => 2 * Real.pi * band n) atTop atTop :=
    band_atTop.const_mul_atTop (by positivity : 0 < 2 * Real.pi)
  have hw : Tendsto (fun n => graphWeight (band n)) atTop atTop := by
    simpa only [graphWeight, Function.comp_def] using
      tendsto_atTop_add_const_left atTop 1 (RhShiftFormContinuity.native_multiplier_atTop.comp ha)
  have ht := tendsto_inv_atTop_zero.comp hw
  have hb := (tendsto_inv_atTop_zero.comp band_atTop).const_mul (64 * Real.pi ^ 2 * R ^ 3)
  change Tendsto (fun n => 1 / graphWeight (band n) + (64 * Real.pi ^ 2 * R ^ 3) / band n) atTop (𝓝 0)
  simpa only [Function.comp_def, one_div, div_eq_mul_inv, mul_zero, add_zero, one_mul] using ht.add hb

def approximation (R : ℝ) (n : ℕ) : SupportedSpace R →L[ℝ] WholeSpace :=
  grid R (band n) (count n)

lemma approximation_error_norm {R : ℝ} (hR : 0 < R) (n : ℕ) :
    ‖frequencyEmbedding R - approximation R n‖ ≤ Real.sqrt (budget R n) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
  intro F
  have he := grid_error_bound hR (band_pos n) (count_pos n) F
  rw [budget_eq R n] at he
  have hs : (Real.sqrt (budget R n) * ‖F‖) ^ 2 = budget R n * ‖F‖ ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (budget_nonneg hR n)]
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  rw [hs]
  exact he

set_option backward.isDefEq.respectTransparency false in
lemma approximation_tendsto {R : ℝ} (hR : 0 < R) :
    Tendsto (approximation R) atTop (𝓝 (frequencyEmbedding R)) := by
  have ht : Tendsto (fun n => ‖frequencyEmbedding R - approximation R n‖) atTop (𝓝 0) :=
    squeeze_zero (fun n => norm_nonneg (frequencyEmbedding R - approximation R n)) (approximation_error_norm hR)
      (by simpa only [Function.comp_def, Real.sqrt_zero] using (Real.continuous_sqrt.tendsto 0).comp (budget_tendsto_zero R))
  exact (tendsto_iff_norm_sub_tendsto_zero (f := approximation R)
    (a := atTop) (b := frequencyEmbedding R)).mpr (by
      have he : (fun n => ‖approximation R n - frequencyEmbedding R‖) =
          (fun n => ‖frequencyEmbedding R - approximation R n‖) := by
        funext n
        exact norm_sub_rev (approximation R n) (frequencyEmbedding R)
      rw [he]
      exact ht)

/-- The full native finite-energy domain has a compact frequency-to-L2 inclusion
on each fixed finite support window. This does not prove the arithmetic form positive. -/
theorem frequency_embedding_compact {R : ℝ} (hR : 0 < R) :
    IsCompactOperator (frequencyEmbedding R) := by
  apply isCompactOperator_of_tendsto (approximation_tendsto hR)
  exact Eventually.of_forall (fun n => grid_compact R (band n) (count n))

/-- Unitary inverse Fourier transfer gives the actual compact spatial embedding. -/
theorem physical_embedding_compact {R : ℝ} (hR : 0 < R) :
    IsCompactOperator (physicalEmbedding.comp (supportedSubspace R).subtypeL) := by
  exact (frequency_embedding_compact hR).clm_comp inverseFourier

end RhSupportedCompactEmbedding
#print axioms RhSupportedCompactEmbedding.grid_error_norm_square
#print axioms RhSupportedCompactEmbedding.budget_tendsto_zero
#print axioms RhSupportedCompactEmbedding.frequency_embedding_compact
#print axioms RhSupportedCompactEmbedding.physical_embedding_compact






