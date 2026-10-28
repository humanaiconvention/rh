import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.MetricSpace.Lipschitz

noncomputable section
open Set MeasureTheory Filter
open scoped Interval NNReal
namespace MeasureTheory

theorem integrable_lipschitz_mul {μ : Measure ℝ} {d w : ℝ → ℝ}
    (hd : Integrable d μ) (hm : Integrable (fun x => x * d x) μ)
    (hw : LipschitzWith 1 w) :
    Integrable (fun x => w x * d x) μ := by
  have hmajor : Integrable (fun x => |w 0| * |d x| + |x * d x|) μ := by
    have hsum := (hd.norm.const_mul |w 0|).add hm.norm
    change Integrable (fun x => |w 0| * ‖d x‖ + ‖x * d x‖) μ at hsum
    simpa only [Real.norm_eq_abs] using hsum
  apply hmajor.mono'
  · have hmeas := hw.continuous.measurable.aestronglyMeasurable.mul hd.aestronglyMeasurable
    change AEStronglyMeasurable (fun x => w x * d x) μ at hmeas
    exact hmeas
  · exact Eventually.of_forall (fun x => by
      change |w x * d x| ≤ |w 0| * |d x| + |x * d x|
      have hlip : |w x - w 0| ≤ |x| := by
        simpa only [Real.dist_eq, sub_zero, NNReal.coe_one, one_mul]
          using hw.dist_le_mul x 0
      have hgrowth : |w x| ≤ |w 0| + |x| := by
        calc
          |w x| = |(w x - w 0) + w 0| := by rw [sub_add_cancel]
          _ ≤ |w x - w 0| + |w 0| := abs_add_le _ _
          _ ≤ |x| + |w 0| := add_le_add hlip (le_refl _)
          _ = |w 0| + |x| := add_comm _ _
      rw [abs_mul, abs_mul]
      calc
        |w x| * |d x| ≤ (|w 0| + |x|) * |d x| :=
          mul_le_mul_of_nonneg_right hgrowth (abs_nonneg _)
        _ = |w 0| * |d x| + |x| * |d x| := add_mul _ _ _)


private def anchor (x t : ℝ) : ℝ :=
  (if x ≤ t then 1 else 0) - (if 0 ≤ t then 1 else 0)

private theorem anchor_joint_measurable :
    Measurable (fun z : ℝ × ℝ => anchor z.1 z.2) := by
  unfold anchor
  exact (Measurable.ite (measurableSet_le measurable_fst measurable_snd)
    measurable_const measurable_const).sub
    (Measurable.ite (measurableSet_le measurable_const measurable_snd)
      measurable_const measurable_const)

private theorem abs_anchor_eq_indicator (x t : ℝ) :
    |anchor x t| =
      (Ico (min 0 x) (max 0 x)).indicator (fun _ : ℝ => (1 : ℝ)) t := by
  by_cases hx : 0 ≤ x
  · rw [min_eq_left hx, max_eq_right hx]
    by_cases h0 : 0 ≤ t
    · by_cases hxt : x ≤ t
      · simp [anchor, h0, hxt, Set.indicator, mem_Ico, not_lt.mpr hxt]
      · simp [anchor, h0, hxt, Set.indicator, mem_Ico, not_le.mp hxt]
    · have hxt : ¬ x ≤ t := fun hxt => h0 (hx.trans hxt)
      simp [anchor, h0, hxt, Set.indicator, mem_Ico]
  · have hx' : x ≤ 0 := (not_le.mp hx).le
    rw [min_eq_right hx', max_eq_left hx']
    by_cases hxt : x ≤ t
    · by_cases h0 : 0 ≤ t
      · simp [anchor, h0, hxt, Set.indicator, mem_Ico, not_lt.mpr h0]
      · simp [anchor, h0, hxt, Set.indicator, mem_Ico, not_le.mp h0]
    · have h0 : ¬ 0 ≤ t := fun h0 => hxt (hx'.trans h0)
      simp [anchor, h0, hxt, Set.indicator, mem_Ico]

private theorem anchor_section_integrable (x : ℝ) :
    Integrable (fun t : ℝ => anchor x t) volume := by
  have hi : Integrable
      ((Ico (min 0 x) (max 0 x)).indicator (fun _ : ℝ => (1 : ℝ))) volume := by
    apply (integrable_indicator_iff measurableSet_Ico).2
    exact integrableOn_const (by simp)
  apply hi.mono'
    (anchor_joint_measurable.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  exact Eventually.of_forall (fun t => by
    simpa only [Real.norm_eq_abs, Function.comp_apply, id_eq] using
      (abs_anchor_eq_indicator x t).le)

private theorem anchor_section_norm_integral (x : ℝ) :
    (∫ t : ℝ, ‖anchor x t‖) = |x| := by
  simp_rw [Real.norm_eq_abs, abs_anchor_eq_indicator]
  rw [integral_indicator_const (1 : ℝ) measurableSet_Ico]
  simp only [smul_eq_mul, mul_one, Real.volume_real_Ico]
  by_cases hx : 0 ≤ x
  · simp [min_eq_left hx, max_eq_right hx, max_eq_left hx, abs_of_nonneg hx]
  · have hx' : x ≤ 0 := (not_le.mp hx).le
    simp [min_eq_right hx', max_eq_left hx', max_eq_left (neg_nonneg.mpr hx'),
      abs_of_nonpos hx']

private theorem anchor_product_integrable {μ : Measure ℝ}
    (hfirst : Integrable (fun x : ℝ => x) μ) :
    Integrable (fun z : ℝ × ℝ => anchor z.1 z.2) (μ.prod volume) := by
  apply (integrable_prod_iff anchor_joint_measurable.aestronglyMeasurable).2
  refine ⟨Eventually.of_forall anchor_section_integrable, ?_⟩
  change Integrable (fun x : ℝ => ∫ t : ℝ, ‖anchor x t‖) μ
  have he : (fun x : ℝ => ∫ t : ℝ, ‖anchor x t‖) = (fun x : ℝ => |x|) :=
    funext anchor_section_norm_integral
  rw [he]
  simpa only [Real.norm_eq_abs] using hfirst.norm

private theorem norm_phase_mul (z : ℝ) : ‖z‖ * (z / ‖z‖) = z := by
  by_cases hz : z = 0
  · simp [hz]
  · have hn : ‖z‖ ≠ 0 := fun h => hz (norm_eq_zero.mp h)
    calc
      ‖z‖ * (z / ‖z‖) = (‖z‖ * z) / ‖z‖ := (mul_div_assoc _ _ _).symm
      _ = z := (div_eq_iff hn).2 (mul_comm _ _)

private theorem phase_norm_le (z : ℝ) : ‖z / ‖z‖‖ ≤ 1 := by
  by_cases hz : z = 0
  · simp [hz]
  · have hn : ‖z‖ ≠ 0 := fun h => hz (norm_eq_zero.mp h)
    change |z / ‖z‖| ≤ 1
    rw [abs_div, abs_of_nonneg (norm_nonneg z), ← Real.norm_eq_abs, div_self hn]

private theorem anchor_signed_integral {ν : Measure ℝ} {s : ℝ → ℝ}
    (hs : Integrable s ν) (t : ℝ) :
    (∫ x, anchor x t * s x ∂ν) =
      (∫ x in Iic t, s x ∂ν) -
        (if 0 ≤ t then (1 : ℝ) else 0) * (∫ x, s x ∂ν) := by
  have he : (fun x : ℝ => (if x ≤ t then (1 : ℝ) else 0) * s x) =
      (Iic t).indicator s := by
    funext x
    by_cases hx : x ≤ t <;> simp [Set.indicator, mem_Iic, hx]
  have hi : Integrable (fun x : ℝ => (if x ≤ t then (1 : ℝ) else 0) * s x) ν := by
    rw [he]
    exact hs.indicator measurableSet_Iic
  have hv : (∫ x, (if x ≤ t then (1 : ℝ) else 0) * s x ∂ν) =
      ∫ x in Iic t, s x ∂ν := by
    rw [he, integral_indicator measurableSet_Iic]
  unfold anchor
  simp_rw [sub_mul]
  rw [integral_sub hi (hs.const_mul _), hv, integral_const_mul]

private theorem density_carrier_data {μ : Measure ℝ} {d : ℝ → ℝ}
    (hd : Integrable d μ) (hm : Integrable (fun x => x * d x) μ) :
    ∃ (ν : Measure ℝ) (σ : ℝ → ℝ), IsFiniteMeasure ν ∧ Measurable σ ∧
      (∀ x, ‖σ x‖ ≤ 1) ∧ Integrable σ ν ∧ Integrable (fun x : ℝ => x) ν ∧
      (∀ s : Set ℝ, MeasurableSet s → (∫ x in s, σ x ∂ν) = ∫ x in s, d x ∂μ) ∧
      (∀ w : ℝ → ℝ, Integrable (fun x => w x * d x) μ →
        (∫ x, w x * σ x ∂ν) = ∫ x, w x * d x ∂μ) := by
  let D : ℝ → ℝ := hd.aestronglyMeasurable.mk d
  have hDm : Measurable D := hd.aestronglyMeasurable.measurable_mk
  have hDd : d =ᵐ[μ] D := hd.aestronglyMeasurable.ae_eq_mk
  have hDI : Integrable D μ := hd.congr hDd
  have hmD : Integrable (fun x => x * D x) μ := by
    apply hm.congr
    filter_upwards [hDd] with x hx
    rw [hx]
  let ν : Measure ℝ := μ.withDensity (fun x => ENNReal.ofReal ‖D x‖)
  have hν : IsFiniteMeasure ν := isFiniteMeasure_withDensity_ofReal hDI.norm.hasFiniteIntegral
  letI := hν
  let σ : ℝ → ℝ := fun x => D x / ‖D x‖
  have hσm : Measurable σ := hDm.div hDm.norm
  have hσbound (x : ℝ) : ‖σ x‖ ≤ 1 := phase_norm_le (D x)
  have hσI : Integrable σ ν := by
    have hone : Integrable (fun _ : ℝ => (1 : ℝ)) ν := integrable_const _
    exact hone.mono' hσm.aestronglyMeasurable (Eventually.of_forall hσbound)
  have hfirst : Integrable (fun x : ℝ => x) ν := by
    have hweighted : Integrable (fun x => ‖D x‖ * x) μ := by
      apply hmD.norm.mono' (hDm.norm.mul measurable_id).aestronglyMeasurable
      exact Eventually.of_forall (fun x => by
        change ‖‖D x‖ * x‖ ≤ ‖x * D x‖
        simpa only [Real.norm_eq_abs, abs_mul, abs_abs]
          using le_of_eq (mul_comm |D x| |x|))
    change Integrable (fun x : ℝ => x) (μ.withDensity (fun x => ENNReal.ofReal ‖D x‖))
    apply (integrable_withDensity_iff_integrable_smul' hDm.norm.ennreal_ofReal
      (Eventually.of_forall (fun x => ENNReal.ofReal_lt_top))).2
    apply hweighted.congr
    exact Eventually.of_forall (fun x => by
      change ‖D x‖ * x = (ENNReal.ofReal ‖D x‖).toReal * x
      rw [ENNReal.toReal_ofReal (norm_nonneg _)])
  have htransfer (s : Set ℝ) (hs : MeasurableSet s) :
      (∫ x in s, σ x ∂ν) = ∫ x in s, d x ∂μ := by
    change (∫ x in s, σ x ∂μ.withDensity (fun x => ENNReal.ofReal ‖D x‖)) = _
    rw [setIntegral_withDensity_eq_setIntegral_toReal_smul hDm.norm.ennreal_ofReal
      (Eventually.of_forall (fun x => ENNReal.ofReal_lt_top)) σ hs]
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae hDd] with x hx
    change (ENNReal.ofReal ‖D x‖).toReal * (D x / ‖D x‖) = d x
    rw [ENNReal.toReal_ofReal (norm_nonneg _), norm_phase_mul, ← hx]
  have hweighted (w : ℝ → ℝ) (_hwi : Integrable (fun x => w x * d x) μ) : (∫ x, w x * σ x ∂ν) = ∫ x, w x * d x ∂μ := by
    change (∫ x, w x * σ x ∂μ.withDensity (fun x => ENNReal.ofReal ‖D x‖)) = _
    rw [integral_withDensity_eq_integral_toReal_smul hDm.norm.ennreal_ofReal
      (Eventually.of_forall (fun x => ENNReal.ofReal_lt_top))]
    apply integral_congr_ae
    filter_upwards [hDd] with x hx
    change (ENNReal.ofReal ‖D x‖).toReal * (w x * (D x / ‖D x‖)) = w x * d x
    rw [ENNReal.toReal_ofReal (norm_nonneg _), mul_left_comm ‖D x‖ (w x),
      norm_phase_mul, ← hx]
  exact ⟨ν, σ, hν, hσm, hσbound, hσI, hfirst, htransfer, hweighted⟩

private theorem anchored_cumulative_data {μ : Measure ℝ} {d : ℝ → ℝ}
    (hd : Integrable d μ) (hm : Integrable (fun x => x * d x) μ)
    (hz : (∫ x, d x ∂μ) = 0) :
    ∃ (ν : Measure ℝ) (σ : ℝ → ℝ), IsFiniteMeasure ν ∧ Measurable σ ∧
      (∀ x, ‖σ x‖ ≤ 1) ∧
      Integrable (fun z : ℝ × ℝ => anchor z.1 z.2 * σ z.1) (ν.prod volume) ∧
      (∀ t : ℝ, (∫ x in Iic t, d x ∂μ) = ∫ x, anchor x t * σ x ∂ν) ∧
      Measurable (fun t : ℝ => ∫ x in Iic t, d x ∂μ) ∧
      Integrable (fun t : ℝ => ∫ x in Iic t, d x ∂μ) volume ∧
      (∀ w : ℝ → ℝ, Integrable (fun x => w x * d x) μ →
        (∫ x, w x * σ x ∂ν) = ∫ x, w x * d x ∂μ) := by
  obtain ⟨ν, σ, hν, hσm, hσbound, hσI, hfirst, htransfer, hweighted⟩ :=
    density_carrier_data hd hm
  letI := hν
  have htotal : (∫ x, σ x ∂ν) = 0 := by
    have ht := htransfer univ MeasurableSet.univ
    simp only [setIntegral_univ] at ht
    exact ht.trans hz
  let F : ℝ × ℝ → ℝ := fun z => anchor z.1 z.2 * σ z.1
  have hFm : Measurable F := anchor_joint_measurable.mul (hσm.comp measurable_fst)
  have hFI : Integrable F (ν.prod volume) := by
    apply (anchor_product_integrable hfirst).norm.mono' hFm.aestronglyMeasurable
    exact Eventually.of_forall (fun z => by
      change ‖anchor z.1 z.2 * σ z.1‖ ≤ ‖anchor z.1 z.2‖
      rw [norm_mul]
      calc
        ‖anchor z.1 z.2‖ * ‖σ z.1‖ ≤ ‖anchor z.1 z.2‖ * 1 :=
          mul_le_mul_of_nonneg_left (hσbound z.1) (norm_nonneg _)
        _ = ‖anchor z.1 z.2‖ := mul_one _)
  have he (t : ℝ) : (∫ x in Iic t, d x ∂μ) = ∫ x, F (x, t) ∂ν := by
    change _ = ∫ x, anchor x t * σ x ∂ν
    rw [anchor_signed_integral hσI t, htotal, mul_zero, sub_zero]
    exact (htransfer (Iic t) measurableSet_Iic).symm
  have hfun : (fun t : ℝ => ∫ x in Iic t, d x ∂μ) =
      (fun t : ℝ => ∫ x, F (x, t) ∂ν) := funext he
  refine ⟨ν, σ, hν, hσm, hσbound, hFI, he, ?_, ?_, hweighted⟩
  · rw [hfun]
    exact hFm.stronglyMeasurable.integral_prod_left'.measurable
  · rw [hfun]
    exact hFI.integral_prod_right

theorem measurable_integrable_setIntegral_Iic {μ : Measure ℝ} {d : ℝ → ℝ}
    (hd : Integrable d μ) (hm : Integrable (fun x => x * d x) μ)
    (hz : (∫ x, d x ∂μ) = 0) :
    Measurable (fun t : ℝ => ∫ x in Iic t, d x ∂μ) ∧
      Integrable (fun t : ℝ => ∫ x in Iic t, d x ∂μ) volume := by
  obtain ⟨ν, σ, hν, hσm, hσbound, hFI, he, hCm, hCI, hweighted⟩ :=
    anchored_cumulative_data hd hm hz
  exact ⟨hCm, hCI⟩

private theorem anchor_mul_of_nonneg (b : ℝ → ℝ) {x : ℝ} (hx : 0 ≤ x) :
    (fun t : ℝ => anchor x t * b t) =
      (fun t : ℝ => -((Ico 0 x).indicator b t)) := by
  funext t
  by_cases h0 : 0 ≤ t
  · by_cases hxt : x ≤ t
    · simp [anchor, h0, hxt, Set.indicator, mem_Ico, not_lt.mpr hxt]
    · simp [anchor, h0, hxt, Set.indicator, mem_Ico, not_le.mp hxt]
  · have hxt : ¬ x ≤ t := fun hxt => h0 (hx.trans hxt)
    simp [anchor, h0, hxt, Set.indicator, mem_Ico]

private theorem anchor_mul_of_nonpos (b : ℝ → ℝ) {x : ℝ} (hx : x ≤ 0) :
    (fun t : ℝ => anchor x t * b t) = (Ico x 0).indicator b := by
  funext t
  by_cases hxt : x ≤ t
  · by_cases h0 : 0 ≤ t
    · simp [anchor, h0, hxt, Set.indicator, mem_Ico, not_lt.mpr h0]
    · simp [anchor, h0, hxt, Set.indicator, mem_Ico, not_le.mp h0]
  · have h0 : ¬ 0 ≤ t := fun h0 => hxt (hx.trans h0)
    simp [anchor, h0, hxt, Set.indicator, mem_Ico]

private theorem bounded_interval_integrable {b : ℝ → ℝ} (hb : Measurable b)
    (hbound : ∀ t : ℝ, |b t| ≤ 1) (a c : ℝ) :
    IntervalIntegrable b volume a c := by
  rw [intervalIntegrable_iff]
  have hc : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (uIoc a c) volume :=
    integrableOn_const (by simp [uIoc])
  change Integrable b (volume.restrict (uIoc a c))
  change Integrable (fun _ : ℝ => (1 : ℝ)) (volume.restrict (uIoc a c)) at hc
  apply hc.mono' hb.aestronglyMeasurable.restrict
  exact Eventually.of_forall (fun t => by
    simpa only [Real.norm_eq_abs] using hbound t)

/-- The endpoint change is in Lebesgue measure t, not in a source measure x.
Actual interval integrability for the intended bounded measurable slopes is
separately supplied above. -/
private theorem kernel_primitive_eq (b : ℝ → ℝ) (x : ℝ) :
    -(∫ t : ℝ, anchor x t * b t) = ∫ t in (0 : ℝ)..x, b t := by
  by_cases hx : 0 ≤ x
  · rw [anchor_mul_of_nonneg b hx, integral_neg, neg_neg,
      integral_indicator measurableSet_Ico, integral_Ico_eq_integral_Ioc,
      intervalIntegral.integral_of_le hx]
  · have hx' : x ≤ 0 := (not_le.mp hx).le
    rw [anchor_mul_of_nonpos b hx', integral_indicator measurableSet_Ico,
      integral_Ico_eq_integral_Ioc, intervalIntegral.integral_of_ge hx']

private theorem primitive_lipschitz {b : ℝ → ℝ} (hb : Measurable b)
    (hbound : ∀ t : ℝ, |b t| ≤ 1) :
    LipschitzWith 1 (fun x : ℝ => ∫ t in (0 : ℝ)..x, b t) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [NNReal.coe_one, one_mul, Real.dist_eq]
  change |(∫ t in (0 : ℝ)..x, b t) - (∫ t in (0 : ℝ)..y, b t)| ≤ |x - y|
  rw [intervalIntegral.integral_interval_sub_left
    (bounded_interval_integrable hb hbound 0 x)
    (bounded_interval_integrable hb hbound 0 y)]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := y) (b := x) (C := (1 : ℝ)) (f := b)
    (fun t _ => by simpa only [Real.norm_eq_abs] using hbound t)
  simpa only [Real.norm_eq_abs, one_mul] using h

private theorem signed_primitive_pairing {μ : Measure ℝ} {d b : ℝ → ℝ}
    (hd : Integrable d μ) (hm : Integrable (fun x => x * d x) μ)
    (hz : (∫ x, d x ∂μ) = 0) (hb : Measurable b) (hbb : ∀ t : ℝ, |b t| ≤ 1) :
    let w : ℝ → ℝ := fun x => ∫ t in (0 : ℝ)..x, b t
    LipschitzWith 1 w ∧ Integrable (fun x => w x * d x) μ ∧
      Integrable (fun t : ℝ => b t * (∫ x in Iic t, d x ∂μ)) volume ∧
      (∫ x, w x * d x ∂μ) = -(∫ t : ℝ, b t * (∫ x in Iic t, d x ∂μ)) := by
  obtain ⟨ν, σ, hν, hσm, hσbound, hFI, he, hCm, hCI, hweighted⟩ :=
    anchored_cumulative_data hd hm hz
  letI := hν
  let C : ℝ → ℝ := fun t => ∫ x in Iic t, d x ∂μ
  let F : ℝ × ℝ → ℝ := fun z => anchor z.1 z.2 * σ z.1
  have hFm : Measurable F := anchor_joint_measurable.mul (hσm.comp measurable_fst)
  change Integrable F (ν.prod volume) at hFI
  let w : ℝ → ℝ := fun x => ∫ t in (0 : ℝ)..x, b t
  have hw : LipschitzWith 1 w := primitive_lipschitz hb hbb
  have hwi : Integrable (fun x => w x * d x) μ := integrable_lipschitz_mul hd hm hw
  let G : ℝ × ℝ → ℝ := fun z => F z * b z.2
  have hGm : Measurable G := hFm.mul (hb.comp measurable_snd)
  have hGI : Integrable G (ν.prod volume) := by
    apply hFI.norm.mono' hGm.aestronglyMeasurable
    exact Eventually.of_forall (fun z => by
      change ‖F z * b z.2‖ ≤ ‖F z‖
      rw [norm_mul]
      calc
        ‖F z‖ * ‖b z.2‖ ≤ ‖F z‖ * 1 :=
          mul_le_mul_of_nonneg_left (by simpa only [Real.norm_eq_abs] using hbb z.2)
            (norm_nonneg _)
        _ = ‖F z‖ := mul_one _)
  have hinner (x : ℝ) : (∫ t : ℝ, G (x, t)) = -(w x * σ x) := by
    have hg : (∫ t : ℝ, G (x, t)) = (∫ t : ℝ, anchor x t * b t) * σ x := by
      calc
        _ = ∫ t : ℝ, (anchor x t * b t) * σ x := by
          apply integral_congr_ae
          exact Eventually.of_forall (fun t => mul_right_comm (anchor x t) (σ x) (b t))
        _ = _ := integral_mul_const _ _
    rw [hg]
    have hp : -(∫ t : ℝ, anchor x t * b t) = w x := kernel_primitive_eq b x
    rw [← hp]
    simp only [neg_mul, neg_neg]
  have hsection (t : ℝ) : (∫ x, G (x, t) ∂ν) = b t * C t := by
    change (∫ x, F (x, t) * b t ∂ν) = b t * C t
    rw [integral_mul_const, ← he t]
    exact mul_comm _ _
  have hcross : (∫ x, w x * σ x ∂ν) = -(∫ t : ℝ, b t * C t) := by
    calc
      _ = -(∫ x, (∫ t : ℝ, G (x, t)) ∂ν) := by
        rw [← integral_neg]
        apply integral_congr_ae
        exact Eventually.of_forall (fun x => by
          change w x * σ x = -(∫ t : ℝ, G (x, t))
          rw [hinner x, neg_neg])
      _ = -(∫ t : ℝ, ∫ x, G (x, t) ∂ν) :=
        congrArg Neg.neg (integral_integral_swap hGI)
      _ = _ := by
        congr 1
        apply integral_congr_ae
        exact Eventually.of_forall hsection
  have hbcI : Integrable (fun t : ℝ => b t * C t) volume := by
    apply hGI.integral_prod_right.congr
    exact Eventually.of_forall hsection
  have hactual := hweighted w hwi
  exact ⟨hw, hwi, hbcI, hactual.symm.trans hcross⟩

/-- Minus the usual real sign, with sign(0)=0; the definition is explicit. -/
private def negativeSign (C : ℝ → ℝ) (t : ℝ) : ℝ :=
  if C t < 0 then 1 else if 0 < C t then -1 else 0

private theorem negativeSign_measurable {C : ℝ → ℝ} (hC : Measurable C) :
    Measurable (negativeSign C) := by
  unfold negativeSign
  exact Measurable.ite (measurableSet_lt hC measurable_const) measurable_const
    (Measurable.ite (measurableSet_lt measurable_const hC) measurable_const measurable_const)

private theorem negativeSign_bound (C : ℝ → ℝ) (t : ℝ) :
    |negativeSign C t| ≤ 1 := by
  unfold negativeSign
  split_ifs <;> simp

private theorem negativeSign_mul (C : ℝ → ℝ) (t : ℝ) :
    negativeSign C t * C t = -|C t| := by
  by_cases hn : C t < 0
  · simp [negativeSign, hn, abs_of_neg hn]
  · by_cases hp : 0 < C t
    · simp [negativeSign, hn, hp, abs_of_pos hp]
    · have hz : C t = 0 := le_antisymm (not_lt.mp hp) (not_lt.mp hn)
      simp [negativeSign, hz]


theorem exists_lipschitz_cumulative_attainer {μ : Measure ℝ} {d : ℝ → ℝ}
    (hd : Integrable d μ) (hm : Integrable (fun x => x * d x) μ)
    (hz : (∫ x, d x ∂μ) = 0) :
    ∃ w : ℝ → ℝ, LipschitzWith 1 w ∧ Integrable (fun x => w x * d x) μ ∧
      (∫ x, w x * d x ∂μ) = ∫ t : ℝ, |∫ x in Iic t, d x ∂μ| := by
  obtain ⟨hCm, hCI⟩ := measurable_integrable_setIntegral_Iic hd hm hz
  let C : ℝ → ℝ := fun t => ∫ x in Iic t, d x ∂μ
  let b : ℝ → ℝ := negativeSign C
  have hb : Measurable b := negativeSign_measurable hCm
  have hbb (t : ℝ) : |b t| ≤ 1 := negativeSign_bound C t
  obtain ⟨hw, hwi, hbcI, he⟩ := signed_primitive_pairing hd hm hz hb hbb
  refine ⟨(fun x => ∫ t in (0 : ℝ)..x, b t), hw, hwi, ?_⟩
  calc
    _ = -(∫ t : ℝ, b t * C t) := he
    _ = ∫ t : ℝ, |C t| := by
      simp_rw [show ∀ t, b t * C t = -|C t| from negativeSign_mul C]
      rw [integral_neg, neg_neg]

private theorem bounded_slope_representation {v : ℝ → ℝ} (hv : LipschitzWith 1 v) :
    ∃ b : ℝ → ℝ, Measurable b ∧ (∀ t : ℝ, |b t| ≤ 1) ∧
      ∀ x : ℝ, v x - v 0 = ∫ t in (0 : ℝ)..x, b t := by
  refine ⟨deriv v, measurable_deriv v, ?_, ?_⟩
  · intro t
    simpa only [Real.norm_eq_abs, NNReal.coe_one] using
      (norm_deriv_le_of_lipschitz (x₀ := t) hv)
  · intro x
    have hl : LipschitzOnWith 1 v (uIcc 0 x) := hv.lipschitzOnWith
    exact hl.absolutelyContinuousOnInterval.integral_deriv_eq_sub.symm

private theorem actual_lipschitz_upper {μ : Measure ℝ} {d v : ℝ → ℝ}
    (hd : Integrable d μ) (hm : Integrable (fun x => x * d x) μ)
    (hz : (∫ x, d x ∂μ) = 0) (hv : LipschitzWith 1 v) :
    Integrable (fun x => v x * d x) μ ∧
      |∫ x, v x * d x ∂μ| ≤ ∫ t : ℝ, |∫ x in Iic t, d x ∂μ| := by
  obtain ⟨hCm, hCI⟩ := measurable_integrable_setIntegral_Iic hd hm hz
  let C : ℝ → ℝ := fun t => ∫ x in Iic t, d x ∂μ
  have hcost : Integrable (fun t => |C t|) volume := by
    simpa only [Real.norm_eq_abs] using hCI.norm
  obtain ⟨b, hb, hbb, hrep⟩ := bounded_slope_representation hv
  let w : ℝ → ℝ := fun x => ∫ t in (0 : ℝ)..x, b t
  obtain ⟨hw, hwi, hbcI, hpair⟩ := signed_primitive_pairing hd hm hz hb hbb
  have hvI : Integrable (fun x => v x * d x) μ := integrable_lipschitz_mul hd hm hv

  have hv_integral : (∫ x, v x * d x ∂μ) = ∫ x, w x * d x ∂μ := by
    calc
      _ = ∫ x, w x * d x + v 0 * d x ∂μ := by
        apply integral_congr_ae
        exact Eventually.of_forall (fun x => by
          change v x * d x = w x * d x + v 0 * d x
          rw [← add_mul]
          have hx : v x - v 0 = w x := hrep x
          rw [← hx, sub_add_cancel])
      _ = (∫ x, w x * d x ∂μ) + v 0 * (∫ x, d x ∂μ) := by
        rw [integral_add hwi (hd.const_mul (v 0)), integral_const_mul]
      _ = _ := by rw [hz, mul_zero, add_zero]
  have hupper : |∫ x, v x * d x ∂μ| ≤ ∫ t : ℝ, |C t| := by
    rw [hv_integral, hpair, abs_neg]
    have hnorm : ∀ᵐ t : ℝ, ‖b t * C t‖ ≤ |C t| :=
      Eventually.of_forall (fun t => by
        change |b t * C t| ≤ |C t|
        rw [abs_mul]
        calc
          |b t| * |C t| ≤ 1 * |C t| :=
            mul_le_mul_of_nonneg_right (hbb t) (abs_nonneg _)
          _ = |C t| := one_mul _)
    simpa only [Real.norm_eq_abs] using norm_integral_le_of_norm_le hcost hnorm
  exact ⟨hvI, hupper⟩

/-- Every REAL budget, with original inclusive density integrals. -/
theorem forall_lipschitz_abs_integral_mul_le_iff {μ : Measure ℝ} {d : ℝ → ℝ}
    (hd : Integrable d μ) (hm : Integrable (fun x => x * d x) μ)
    (hz : (∫ x, d x ∂μ) = 0) (B : ℝ) :
    (∀ w : ℝ → ℝ, LipschitzWith 1 w → |∫ x, w x * d x ∂μ| ≤ B) ↔
      (∫ t : ℝ, |∫ x in Iic t, d x ∂μ|) ≤ B := by
  constructor
  · intro hB
    obtain ⟨w, hw, hwi, he⟩ := exists_lipschitz_cumulative_attainer hd hm hz
    have h := hB w hw
    rw [he] at h
    exact (le_abs_self _).trans h
  · intro hB w hw
    exact ((actual_lipschitz_upper hd hm hz hw).2).trans hB


end MeasureTheory
#print axioms MeasureTheory.integrable_lipschitz_mul
#print axioms MeasureTheory.measurable_integrable_setIntegral_Iic
#print axioms MeasureTheory.exists_lipschitz_cumulative_attainer
#print axioms MeasureTheory.forall_lipschitz_abs_integral_mul_le_iff
