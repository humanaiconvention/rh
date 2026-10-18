import RhFiniteFourierGrid001
import RhWeightedFrequencyTail001

/-! Exact finite-grid L2 error estimate for the actual native Fourier graph
space. This controls compactness, not any signed arithmetic Schur residual. -/
noncomputable section
open Set MeasureTheory Filter FourierTransform
open scoped Topology BigOperators
namespace RhFourierGridError
open RhFiniteFourierGrid RhSupportedMollifier RhWeightedMeasureEmbedding
open RhWeightedEnergyIdentity RhSupportedFourierBound

lemma step_memLp (Omega : ℝ) (M : ℕ) (g : ℝ → ℂ) : MemLp (step Omega M g) 2 volume := by
  classical
  apply memLp_finsetSum
  intro i _
  exact memLp_indicator_const 2 measurableSet_Ico.nullMeasurableSet _
    (Or.inr (measure_Ico_lt_top).ne)

lemma raw_fourier_memLp {R : ℝ} (F : SupportedSpace R) :
    MemLp (𝓕 (representative R F)) 2 volume := by
  have h := RhTail.integral_fourier_ae_L2 (representative_integrable F)
    (representative_memLp F)
  exact (memLp_congr_ae h).mpr (Lp.memLp _)

lemma raw_error_integrable {R : ℝ} (F : SupportedSpace R) (Omega : ℝ) (M : ℕ) :
    Integrable (fun xi => ‖(𝓕 (representative R F)) xi -
      step Omega M (𝓕 (representative R F)) xi‖ ^ 2) volume := by
  have h := (raw_fourier_memLp F).sub (step_memLp Omega M (𝓕 (representative R F)))
  exact (memLp_two_iff_integrable_sq_norm h.aestronglyMeasurable).mp h

/-- On the low-frequency band, the EXACT step error is paid by the cell width. -/
theorem low_band_error {R Omega : ℝ} (hR : 0 < R) (hO : 0 < Omega)
    {M : ℕ} (hM : 0 < M) (F : SupportedSpace R) :
    (∫ xi in Ico (-Omega) Omega, ‖(𝓕 (representative R F)) xi -
      step Omega M (𝓕 (representative R F)) xi‖ ^ 2) ≤
      (64 * Real.pi ^ 2 * R ^ 3 * Omega ^ 3 / M ^ 2) * ‖(F : WeightedSpace)‖ ^ 2 := by
  have hpoint (xi : ℝ) (hxi : xi ∈ Ico (-Omega) Omega) :
      ‖(𝓕 (representative R F)) xi - step Omega M (𝓕 (representative R F)) xi‖ ^ 2 ≤
      (8 * Real.pi ^ 2 * R ^ 3 * width Omega M ^ 2) * ‖(F : WeightedSpace)‖ ^ 2 := by
    obtain ⟨i, hi, _⟩ := unique_cell hO hM hxi
    rw [step_eq_at_cell hO hM hxi hi]
    have h := actual_fourier_increment_square hR F xi (left Omega M i)
    have hd := cell_distance hO hM hi
    have hd2 := (sq_le_sq₀ (abs_nonneg _) (width_pos hO hM).le).2 hd
    exact h.trans (by gcongr)
  have hc : IntegrableOn (fun _ : ℝ =>
      (8 * Real.pi ^ 2 * R ^ 3 * width Omega M ^ 2) * ‖(F : WeightedSpace)‖ ^ 2)
      (Ico (-Omega) Omega) := integrableOn_const measure_Ico_lt_top.ne
  have hmono := integral_mono_ae (raw_error_integrable F Omega M).integrableOn hc
    ((ae_restrict_mem measurableSet_Ico).mono (fun xi hxi => hpoint xi hxi))
  calc
    _ ≤ ∫ _xi in Ico (-Omega) Omega,
      (8 * Real.pi ^ 2 * R ^ 3 * width Omega M ^ 2) * ‖(F : WeightedSpace)‖ ^ 2 := hmono
    _ = _ := by
      rw [integral_const]
      simp only [Measure.real, Measure.restrict_apply_univ, Real.volume_Ico, ENNReal.toReal_ofReal (by linarith : 0 ≤ Omega - -Omega), smul_eq_mul]
      unfold width
      field_simp
      <;> ring

end RhFourierGridError
#print axioms RhFourierGridError.step_memLp
#print axioms RhFourierGridError.low_band_error
