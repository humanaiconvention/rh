import RhShiftFormContinuity001
import RhWeightedEnergyIdentity001
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! Actual weighted-L2 transfer of the native shift-symbol continuity.
The signed two-shift symbol is retained inside one integrable bilinear integral.
This is form-topology continuity, not positivity or a Schur residual estimate. -/
set_option maxHeartbeats 0
noncomputable section
open MeasureTheory Filter FourierTransform
open scoped Topology ENNReal
namespace RhWeightedShiftBilinear
open RhWeightedMeasureEmbedding RhWeightedEnergyIdentity

def graphWeight (xi : ℝ) : ℝ :=
  1 + RhDilationScalar.archMultiplier (1 / 2) (2 * Real.pi * xi)

def shiftSymbol (ell ell' xi : ℝ) : ℝ :=
  2 * (Real.cos ((2 * Real.pi * xi) * ell') -
    Real.cos ((2 * Real.pi * xi) * ell))

def normalizedSymbol (ell ell' xi : ℝ) : ℝ :=
  shiftSymbol ell ell' xi / graphWeight xi

lemma graphWeight_positive (xi : ℝ) : 0 < graphWeight xi := by
  have h := RhShiftFormMultiplier.archMultiplier_nonneg
    (b := 1 / 2) (omega := 2 * Real.pi * xi) (by norm_num)
  unfold graphWeight
  linarith

lemma archWeight_real (xi : ℝ) : (archWeight xi).toReal = graphWeight xi := by
  rw [archWeight_eq, ENNReal.toReal_add (by norm_num) ENNReal.ofReal_ne_top,
    ENNReal.toReal_one, ENNReal.toReal_ofReal]
  · rfl
  · exact RhShiftFormMultiplier.archMultiplier_nonneg (by norm_num)

lemma graphWeight_measurable : Measurable graphWeight := by
  have he : (fun xi => (archWeight xi).toReal) = graphWeight := funext archWeight_real
  rw [← he]
  exact archWeight_measurable.ennreal_toReal

lemma normalizedSymbol_measurable (ell ell' : ℝ) :
    Measurable (normalizedSymbol ell ell') := by
  unfold normalizedSymbol
  apply Measurable.div _ graphWeight_measurable
  unfold shiftSymbol
  fun_prop

lemma norm_product_integrable (F G : WeightedSpace) :
    Integrable (fun xi => ‖F xi‖ * ‖G xi‖) weightedMeasure :=
  (Lp.memLp F).norm.integrable_mul (Lp.memLp G).norm

lemma norm_product_integral_le (F G : WeightedSpace) :
    (∫ xi, ‖F xi‖ * ‖G xi‖ ∂weightedMeasure) ≤ ‖F‖ * ‖G‖ := by
  let NF : Lp (α := ℝ) ℝ 2 weightedMeasure :=
    ((Lp.memLp F).norm).toLp (fun xi => ‖F xi‖)
  let NG : Lp (α := ℝ) ℝ 2 weightedMeasure :=
    ((Lp.memLp G).norm).toLp (fun xi => ‖G xi‖)
  have hNF : ‖NF‖ = ‖F‖ := by
    rw [Lp.norm_toLp, eLpNorm_norm F (Lp.memLp F).aestronglyMeasurable]
    rfl
  have hNG : ‖NG‖ = ‖G‖ := by
    rw [Lp.norm_toLp, eLpNorm_norm G (Lp.memLp G).aestronglyMeasurable]
    rfl
  have he : (∫ xi, ‖F xi‖ * ‖G xi‖ ∂weightedMeasure) =
      inner ℝ NF NG := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [MemLp.coeFn_toLp (Lp.memLp F).norm,
      MemLp.coeFn_toLp (Lp.memLp G).norm] with xi hf hg
    simp only [NF, NG] at hf hg ⊢
    rw [hf, hg]
    simp only [Real.inner_apply, mul_comm]
  rw [he, ← hNF, ← hNG]
  exact real_inner_le_norm NF NG

lemma weighted_bilinear_estimate (ell ell' eta : ℝ) (heta : 0 ≤ eta)
    (hbudget : ∀ xi, |normalizedSymbol ell ell' xi| ≤ eta)
    (F G : WeightedSpace) :
    Integrable (fun xi => normalizedSymbol ell ell' xi *
      inner ℝ (F xi) (G xi)) weightedMeasure ∧
    |∫ xi, normalizedSymbol ell ell' xi * inner ℝ (F xi) (G xi)
      ∂weightedMeasure| ≤ eta * ‖F‖ * ‖G‖ := by
  have hdom : ∀ xi, ‖normalizedSymbol ell ell' xi *
      inner ℝ (F xi) (G xi)‖ ≤ eta * (‖F xi‖ * ‖G xi‖) := by
    intro xi
    rw [norm_mul]
    exact (mul_le_mul (hbudget xi) (abs_real_inner_le_norm _ _)
      (abs_nonneg _) heta).trans_eq (by ring)
  have hmajor := (norm_product_integrable F G).const_mul eta
  have hi : Integrable (fun xi => normalizedSymbol ell ell' xi *
      inner ℝ (F xi) (G xi)) weightedMeasure := by
    apply hmajor.mono' _
      (Eventually.of_forall hdom)
    exact (normalizedSymbol_measurable ell ell').aestronglyMeasurable.mul
      ((Lp.memLp F).aestronglyMeasurable.inner (Lp.memLp G).aestronglyMeasurable)
  refine ⟨hi, ?_⟩
  calc
    _ ≤ ∫ xi, ‖normalizedSymbol ell ell' xi * inner ℝ (F xi) (G xi)‖
        ∂weightedMeasure := norm_integral_le_integral_norm _
    _ ≤ ∫ xi, eta * (‖F xi‖ * ‖G xi‖) ∂weightedMeasure :=
      integral_mono hi.norm hmajor hdom
    _ = eta * (∫ xi, ‖F xi‖ * ‖G xi‖ ∂weightedMeasure) := integral_const_mul _ _
    _ ≤ eta * (‖F‖ * ‖G‖) := mul_le_mul_of_nonneg_left
      (norm_product_integral_le F G) heta
    _ = eta * ‖F‖ * ‖G‖ := by ring

lemma weighted_to_native_integral (ell ell' : ℝ) (F G : WeightedSpace)
    (hi : Integrable (fun xi => normalizedSymbol ell ell' xi *
      inner ℝ (F xi) (G xi)) weightedMeasure) :
    Integrable (fun xi => shiftSymbol ell ell' xi *
      inner ℝ (F xi) (G xi)) volume ∧
    (∫ xi, normalizedSymbol ell ell' xi * inner ℝ (F xi) (G xi)
      ∂weightedMeasure) =
    (∫ xi, shiftSymbol ell ell' xi * inner ℝ (F xi) (G xi)) := by
  have hc : (fun xi => (archWeight xi).toReal •
      (normalizedSymbol ell ell' xi * inner ℝ (F xi) (G xi))) =
      (fun xi => shiftSymbol ell ell' xi * inner ℝ (F xi) (G xi)) := by
    funext xi
    rw [smul_eq_mul, archWeight_real]
    unfold normalizedSymbol
    field_simp [ne_of_gt (graphWeight_positive xi)]
  have ht : ∀ᵐ xi ∂volume, archWeight xi < ⊤ :=
    Eventually.of_forall (fun xi => lt_top_iff_ne_top.mpr (archWeight_ne_top xi))
  have hh := (integrable_withDensity_iff_integrable_smul'
    archWeight_measurable ht).mp hi
  rw [hc] at hh
  refine ⟨hh, ?_⟩
  change (∫ xi, _ ∂volume.withDensity archWeight) = _
  rw [integral_withDensity_eq_integral_toReal_smul archWeight_measurable ht, hc]

/-- Genuine native Fourier shift continuity with all integrability obligations
and the actual physical Fourier representatives explicitly retained. -/
theorem uniform_actual_shift_bilinear {eta : ℝ} (heta : 0 < eta) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ (ell ell' : ℝ), |ell' - ell| < delta →
      ∀ (F G : WeightedSpace),
      Integrable (fun xi => shiftSymbol ell ell' xi *
        inner ℝ ((𝓕 (physicalEmbedding F) : WholeSpace) xi)
          ((𝓕 (physicalEmbedding G) : WholeSpace) xi)) volume ∧
      |∫ xi, shiftSymbol ell ell' xi *
        inner ℝ ((𝓕 (physicalEmbedding F) : WholeSpace) xi)
          ((𝓕 (physicalEmbedding G) : WholeSpace) xi)| ≤
        eta * ‖F‖ * ‖G‖ := by
  obtain ⟨delta, hdelta, hd⟩ := RhShiftFormContinuity.uniform_native_shift_budget heta
  refine ⟨delta, hdelta, ?_⟩
  intro ell ell' hshift F G
  have hb : ∀ xi, |normalizedSymbol ell ell' xi| ≤ eta := by
    intro xi
    have hh := hd ell ell' (2 * Real.pi * xi) hshift
    change |shiftSymbol ell ell' xi| < eta * graphWeight xi at hh
    unfold normalizedSymbol
    rw [abs_div, abs_of_pos (graphWeight_positive xi)]
    exact ((div_lt_iff₀ (graphWeight_positive xi)).mpr hh).le
  obtain ⟨hi, hbound⟩ := weighted_bilinear_estimate ell ell' eta heta.le hb F G
  obtain ⟨hj, he⟩ := weighted_to_native_integral ell ell' F G hi
  have hrep : (fun xi => shiftSymbol ell ell' xi *
      inner ℝ ((𝓕 (physicalEmbedding F) : WholeSpace) xi)
        ((𝓕 (physicalEmbedding G) : WholeSpace) xi)) =ᵐ[volume]
      (fun xi => shiftSymbol ell ell' xi * inner ℝ (F xi) (G xi)) := by
    rw [physicalEmbedding_fourier, physicalEmbedding_fourier]
    filter_upwards [inclusion_ae F, inclusion_ae G] with xi hf hg
    rw [hf, hg]
  exact ⟨hj.congr hrep.symm, by rw [integral_congr_ae hrep, ← he]; exact hbound⟩

end RhWeightedShiftBilinear
#print axioms RhWeightedShiftBilinear.norm_product_integral_le
#print axioms RhWeightedShiftBilinear.weighted_to_native_integral
#print axioms RhWeightedShiftBilinear.uniform_actual_shift_bilinear
