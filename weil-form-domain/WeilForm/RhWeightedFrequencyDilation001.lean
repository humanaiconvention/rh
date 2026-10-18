import RhWeightedDilationInverse001
import RhWeightedFrequencyDensity001

/-! Actual frequency dilation on the WHOLE native weighted L2 space. This
module does not infer spatial support from frequency smoothness. The native
five-log scalar inequality supplies the exact rescaled-weight bound. -/
set_option maxHeartbeats 0
noncomputable section
open Set MeasureTheory Filter FourierTransform
open scoped Topology ENNReal
namespace RhWeightedFrequencyDilation
open RhDilation RhDilationScalar RhWeightedMeasureEmbedding RhWeightedEnergyIdentity
open RhDilationContraction RhWeightedDilation

lemma archWeight_ofReal (xi : ℝ) : archWeight xi = ENNReal.ofReal
    (1 + archMultiplier (1 / 2) (2 * Real.pi * xi)) := by
  have hm : 0 ≤ archMultiplier (1 / 2) (2 * Real.pi * xi) :=
    RhShiftFormMultiplier.archMultiplier_nonneg (by norm_num)
  rw [archWeight_eq, ENNReal.ofReal_add (by norm_num) hm]
  norm_num

lemma archWeight_scale_bound {r : ℝ} (hr : 1 ≤ r) (xi : ℝ) :
    archWeight (r * xi) ≤ ENNReal.ofReal (1 + 5 * Real.log r) * archWeight xi := by
  have hr0 : 0 < r := by linarith
  have h0 : 0 ≤ archMultiplier (1 / 2) (2 * Real.pi * xi) :=
    RhShiftFormMultiplier.archMultiplier_nonneg (by norm_num)
  have hl : 0 ≤ Real.log r := Real.log_nonneg hr
  have hs := (beta_half_scaling hr (r * (2 * Real.pi * xi))).2
  have hd : r * (2 * Real.pi * xi) / r = 2 * Real.pi * xi := by field_simp
  rw [hd] at hs
  have he : 2 * Real.pi * (r * xi) = r * (2 * Real.pi * xi) := by ring
  rw [archWeight_ofReal, archWeight_ofReal, ← ENNReal.ofReal_mul (by linarith)]
  apply ENNReal.ofReal_le_ofReal
  rw [he]
  nlinarith [mul_nonneg hl h0]

lemma lintegral_comp_div {r : ℝ} (hr : 0 < r) (g : ℝ → ℝ≥0∞) :
    (∫⁻ t, g (t / r)) = ENNReal.ofReal r * ∫⁻ t, g t := by
  have he := (Homeomorph.mulLeft₀ r⁻¹ (inv_ne_zero hr.ne')).toMeasurableEquiv.measurableEmbedding.lintegral_map (μ := volume) g
  change (∫⁻ t, g t ∂Measure.map (fun x : ℝ => r⁻¹ * x) volume) =
    ∫⁻ t, g (r⁻¹ * t) at he
  rw [Real.map_volume_mul_left (inv_ne_zero hr.ne'), lintegral_smul_measure,
    inv_inv, abs_of_pos hr] at he
  simpa only [div_eq_mul_inv, mul_comm, smul_eq_mul] using he.symm

lemma weighted_scaled_square {r : ℝ} (hr : 0 < r) {f : ℝ → ℂ} (hf : Measurable f) :
    (∫⁻ xi, ENNReal.ofReal (‖complexDilate r f xi‖ ^ 2) ∂weightedMeasure) =
      ∫⁻ xi, archWeight (r * xi) * ENNReal.ofReal (‖f xi‖ ^ 2) := by
  have hm : Measurable (complexDilate r f) := by
    unfold complexDilate
    exact measurable_const.mul (hf.comp (measurable_id.div_const r))
  rw [weightedMeasure, lintegral_withDensity_eq_lintegral_mul volume archWeight_measurable
    (hm.norm.pow_const 2).ennreal_ofReal]
  simp only [Pi.mul_apply]
  let g : ℝ → ℝ≥0∞ := fun xi => archWeight (r * xi) * ENNReal.ofReal (‖f xi‖ ^ 2)
  have he : (fun xi => archWeight xi * ENNReal.ofReal (‖complexDilate r f xi‖ ^ 2)) =
      fun xi => ENNReal.ofReal r⁻¹ * g (xi / r) := by
    funext xi
    rw [complexDilate_norm_square hr, ENNReal.ofReal_mul (inv_nonneg.mpr hr.le)]
    have hx : r * (xi / r) = xi := by field_simp
    simp only [g, hx]
    ring
  rw [he, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_comp_div hr,
    ← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.mpr hr.le), inv_mul_cancel₀ hr.ne']
  simp only [ENNReal.ofReal_one, one_mul, g]

/-- Exact whole-space norm-square majorant before real conversion. -/
theorem frequency_dilate_square_bound {r : ℝ} (hr : 1 ≤ r) (F : WeightedSpace) :
    (∫⁻ xi, ENNReal.ofReal (‖complexDilate r F xi‖ ^ 2) ∂weightedMeasure) ≤
      ENNReal.ofReal (1 + 5 * Real.log r) * ENNReal.ofReal (‖F‖ ^ 2) := by
  rw [weighted_scaled_square (by linarith : 0 < r) (Lp.stronglyMeasurable F).measurable]
  calc
    _ ≤ ∫⁻ xi, ENNReal.ofReal (1 + 5 * Real.log r) *
        (archWeight xi * ENNReal.ofReal (‖F xi‖ ^ 2)) := by
      apply lintegral_mono
      intro xi
      dsimp only
      rw [← mul_assoc]
      exact mul_le_mul' (archWeight_scale_bound hr xi) le_rfl
    _ = _ := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      have hm : Measurable (fun xi => ENNReal.ofReal (‖F xi‖ ^ 2)) :=
        ((Lp.stronglyMeasurable F).measurable.norm.pow_const 2).ennreal_ofReal
      have hi : (∫⁻ xi, archWeight xi * ENNReal.ofReal (‖F xi‖ ^ 2)) =
          ∫⁻ xi, ENNReal.ofReal (‖F xi‖ ^ 2) ∂weightedMeasure := by
        simpa only [Pi.mul_apply, weightedMeasure] using
          (lintegral_withDensity_eq_lintegral_mul volume archWeight_measurable hm).symm
      rw [hi, lp_lintegral_norm_sq F]

lemma frequency_dilate_memLp {r : ℝ} (hr : 1 ≤ r) (F : WeightedSpace) :
    MemLp (complexDilate r F) 2 weightedMeasure := by
  have hm : Measurable (complexDilate r F) := by
    unfold complexDilate
    exact measurable_const.mul ((Lp.stronglyMeasurable F).measurable.comp
      (measurable_id.div_const r))
  apply (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mpr
  refine ⟨hm.norm.pow_const 2 |>.aestronglyMeasurable, ?_⟩
  apply (hasFiniteIntegral_iff_ofReal (Eventually.of_forall (fun _ => sq_nonneg _))).mpr
  exact lt_of_le_of_lt (frequency_dilate_square_bound hr F)
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)

def frequencyDilate {r : ℝ} (hr : 1 ≤ r) (F : WeightedSpace) : WeightedSpace :=
  (frequency_dilate_memLp hr F).toLp (complexDilate r F)

lemma frequencyDilate_ae {r : ℝ} (hr : 1 ≤ r) (F : WeightedSpace) :
    frequencyDilate hr F =ᵐ[weightedMeasure] complexDilate r F :=
  (frequency_dilate_memLp hr F).coeFn_toLp

lemma frequencyDilate_norm_square_le {r : ℝ} (hr : 1 ≤ r) (F : WeightedSpace) :
    ‖frequencyDilate hr F‖ ^ 2 ≤ (1 + 5 * Real.log r) * ‖F‖ ^ 2 := by
  have hle := frequency_dilate_square_bound hr F
  have he : (∫⁻ xi, ENNReal.ofReal (‖complexDilate r F xi‖ ^ 2) ∂weightedMeasure) =
      ENNReal.ofReal (‖frequencyDilate hr F‖ ^ 2) := by
    rw [← lp_lintegral_norm_sq]
    apply lintegral_congr_ae
    filter_upwards [frequencyDilate_ae hr F] with xi hxi
    rw [hxi]
  rw [he, ← ENNReal.ofReal_mul (show 0 ≤ 1 + 5 * Real.log r from by
    have hl := Real.log_nonneg hr; linarith)] at hle
  have hc : 0 ≤ 1 + 5 * Real.log r := by
    have hl := Real.log_nonneg hr; linarith
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hc (sq_nonneg _))).mp hle

end RhWeightedFrequencyDilation
#print axioms RhWeightedFrequencyDilation.archWeight_scale_bound
#print axioms RhWeightedFrequencyDilation.weighted_scaled_square
#print axioms RhWeightedFrequencyDilation.frequency_dilate_memLp
#print axioms RhWeightedFrequencyDilation.frequencyDilate_norm_square_le
