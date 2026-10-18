import RhFourierGridError001

/-! Full actual Fourier finite-grid error: the interior discretization and
native high-frequency energy remain exact, with no arithmetic sign claim. -/
noncomputable section
open Set MeasureTheory Filter FourierTransform
open scoped Topology BigOperators
namespace RhFourierGridGlobalError
open RhFiniteFourierGrid RhSupportedMollifier RhWeightedMeasureEmbedding
open RhWeightedEnergyIdentity RhWeightedFrequencyTail RhFourierGridError
open RhWeightedShiftBilinear

lemma raw_fourier_ae {R : ℝ} (F : SupportedSpace R) :
    (𝓕 (representative R F)) =ᵐ[volume] (F : WeightedSpace) := by
  have h := RhTail.integral_fourier_ae_L2 (representative_integrable F) (representative_memLp F)
  rw [← representative_toLp F, physicalEmbedding_fourier] at h
  exact h.trans (inclusion_ae (F : WeightedSpace))

lemma outside_band_mass {R Omega : ℝ} (hO : 0 < Omega) (F : SupportedSpace R) :
    (∫ xi in (Ico (-Omega) Omega)ᶜ, ‖(F : WeightedSpace) xi‖ ^ 2) ≤
      ‖(F : WeightedSpace)‖ ^ 2 / graphWeight Omega := by
  let S := (Ico (-Omega) Omega)ᶜ
  have hF : MemLp (fun xi => (F : WeightedSpace) xi) 2 volume :=
    (Lp.memLp (F : WeightedSpace)).mono_measure volume_le_weightedMeasure
  have hmass := (memLp_two_iff_integrable_sq_norm hF.aestronglyMeasurable).mp hF
  have hw := weighted_square_integrable (F : WeightedSpace)
  have hpoint (xi : ℝ) (hxi : xi ∈ S) : graphWeight Omega ≤ graphWeight xi := by
    apply graphWeight_mono_outside hO.le
    by_contra hn
    have ha := abs_lt.mp (lt_of_not_ge hn)
    exact hxi ⟨ha.1.le, ha.2⟩
  have hle : graphWeight Omega * (∫ xi in S, ‖(F : WeightedSpace) xi‖ ^ 2) ≤
      ∫ xi in S, graphWeight xi * ‖(F : WeightedSpace) xi‖ ^ 2 := by
    rw [← integral_const_mul]
    apply integral_mono_ae (hmass.integrableOn.const_mul _) hw.integrableOn
    filter_upwards [ae_restrict_mem measurableSet_Ico.compl] with xi hxi
    exact mul_le_mul_of_nonneg_right (hpoint xi hxi) (sq_nonneg _)
  have htotal : (∫ xi in S, graphWeight xi * ‖(F : WeightedSpace) xi‖ ^ 2) ≤
      ‖(F : WeightedSpace)‖ ^ 2 := by
    rw [← weighted_square_integral (F : WeightedSpace)]
    exact setIntegral_le_integral hw (Eventually.of_forall (fun xi =>
      mul_nonneg (graphWeight_positive xi).le (sq_nonneg _)))
  apply (le_div_iff₀ (graphWeight_positive Omega)).mpr
  simpa only [mul_comm] using hle.trans htotal

theorem high_band_error {R Omega : ℝ} (hO : 0 < Omega)
    {M : ℕ} (hM : 0 < M) (F : SupportedSpace R) :
    (∫ xi in (Ico (-Omega) Omega)ᶜ, ‖(𝓕 (representative R F)) xi -
      step Omega M (𝓕 (representative R F)) xi‖ ^ 2) ≤
      ‖(F : WeightedSpace)‖ ^ 2 / graphWeight Omega := by
  have he : (∫ xi in (Ico (-Omega) Omega)ᶜ, ‖(𝓕 (representative R F)) xi -
      step Omega M (𝓕 (representative R F)) xi‖ ^ 2) =
      ∫ xi in (Ico (-Omega) Omega)ᶜ, ‖(F : WeightedSpace) xi‖ ^ 2 := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ico.compl,
      ae_restrict_of_ae (raw_fourier_ae F)] with xi hxi hx
    rw [step_zero_outside hO hM hxi, sub_zero, hx]
  rw [he]
  exact outside_band_mass hO F

/-- Explicit whole-space squared error bound, in the true complete native norm. -/
theorem full_grid_error {R Omega : ℝ} (hR : 0 < R) (hO : 0 < Omega)
    {M : ℕ} (hM : 0 < M) (F : SupportedSpace R) :
    (∫ xi, ‖(𝓕 (representative R F)) xi -
      step Omega M (𝓕 (representative R F)) xi‖ ^ 2) ≤
      (1 / graphWeight Omega + 64 * Real.pi ^ 2 * R ^ 3 * Omega ^ 3 / M ^ 2) *
        ‖(F : WeightedSpace)‖ ^ 2 := by
  rw [← integral_add_compl measurableSet_Ico (raw_error_integrable F Omega M)]
  have hlo := low_band_error hR hO hM F
  have hhi := high_band_error hO hM F
  calc
    _ ≤ (64 * Real.pi ^ 2 * R ^ 3 * Omega ^ 3 / M ^ 2) * ‖(F : WeightedSpace)‖ ^ 2 +
      ‖(F : WeightedSpace)‖ ^ 2 / graphWeight Omega := add_le_add hlo hhi
    _ = _ := by ring

end RhFourierGridGlobalError
#print axioms RhFourierGridGlobalError.raw_fourier_ae
#print axioms RhFourierGridGlobalError.outside_band_mass
#print axioms RhFourierGridGlobalError.full_grid_error
