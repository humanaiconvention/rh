import RhFourierSupportBound001
import RhDilationRankL2001

/-! Quantitative phase regularity of the ACTUAL supported weighted domain.
These are auxiliary compactness estimates, not signed-prime cancellation. -/
noncomputable section
open Set MeasureTheory Filter FourierTransform
open scoped Topology
namespace RhSupportedFourierBound
open RhWeightedMeasureEmbedding RhWeightedEnergyIdentity RhSupportedMollifier

lemma representative_norm_square {R : ℝ} (F : SupportedSpace R) :
    (∫ t, ‖representative R F t‖ ^ 2) = ‖physicalEmbedding (F : WeightedSpace)‖ ^ 2 := by
  rw [lp_norm_sq_integral]
  apply integral_congr_ae
  filter_upwards [representative_ae F] with t ht
  rw [ht]

lemma representative_l1_square {R : ℝ} (hR : 0 < R) (F : SupportedSpace R) :
    (∫ t, ‖representative R F t‖) ^ 2 ≤
      2 * R * ‖physicalEmbedding (F : WeightedSpace)‖ ^ 2 := by
  have hm : MemLp (fun t => ‖representative R F t‖) 2 (RhAnchored.physicalMeasure R) :=
    (representative_memLp F).norm.mono_measure Measure.restrict_le_self
  have hi := RhDilationRank.l1_sq_le hR hm
  have hz (t : ℝ) (ht : t ∉ Icc (-R) R) : representative R F t = 0 := by
    simp [representative, ht]
  have h1 : (∫ t in Icc (-R) R, ‖representative R F t‖) =
      ∫ t, ‖representative R F t‖ :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun t ht => by rw [hz t ht, norm_zero])
  have h2 : (∫ t in Icc (-R) R, ‖representative R F t‖ ^ 2) =
      ‖physicalEmbedding (F : WeightedSpace)‖ ^ 2 := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun t ht => by rw [hz t ht, norm_zero, zero_pow (by norm_num : 2 ≠ 0)]),
      representative_norm_square]
  simp only [RhAnchored.interval, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] at hi
  rw [h1, h2] at hi
  exact hi

/-- Squared exact Fourier increment bound, uniform on the graph unit ball. -/
theorem actual_fourier_increment_square {R : ℝ} (hR : 0 < R)
    (F : SupportedSpace R) (xi eta : ℝ) :
    ‖(𝓕 (representative R F)) xi - (𝓕 (representative R F)) eta‖ ^ 2 ≤
      (8 * Real.pi ^ 2 * R ^ 3 * |xi - eta| ^ 2) * ‖(F : WeightedSpace)‖ ^ 2 := by
  have h := RhFourierSupportBound.fourier_lipschitz_of_support hR.le
    (representative_integrable F) (representative_support F) xi eta
  have hL : 0 ≤ ∫ t, ‖representative R F t‖ := integral_nonneg (fun _ => norm_nonneg _)
  have ha : 0 ≤ 2 * Real.pi * R * |xi - eta| := by positivity
  have hs := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg ha hL)).2 h
  have hL2 := representative_l1_square hR F
  have hp := physicalEmbedding_norm_apply_le (F : WeightedSpace)
  have hp2 := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2 hp
  calc
    _ ≤ (2 * Real.pi * R * |xi - eta|) ^ 2 *
        (∫ t, ‖representative R F t‖) ^ 2 := by nlinarith [hs]
    _ ≤ (2 * Real.pi * R * |xi - eta|) ^ 2 *
        (2 * R * ‖physicalEmbedding (F : WeightedSpace)‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hL2 (sq_nonneg _)
    _ ≤ (2 * Real.pi * R * |xi - eta|) ^ 2 *
        (2 * R * ‖(F : WeightedSpace)‖ ^ 2) := by gcongr
    _ = _ := by ring

end RhSupportedFourierBound
#print axioms RhSupportedFourierBound.representative_l1_square
#print axioms RhSupportedFourierBound.actual_fourier_increment_square
