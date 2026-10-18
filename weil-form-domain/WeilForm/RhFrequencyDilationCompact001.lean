import RhWeightedFrequencyDensity001
import RhDilationFourier001
import RhDilationPhysical001
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Direct strong convergence on compact continuous frequency representatives.
The dominating compact set is uniform for 1<=r_n<=2 and has finite actual
native weighted measure. No spatial support statement is inferred. -/
set_option maxHeartbeats 0
noncomputable section
open Set MeasureTheory Filter
open scoped Topology ENNReal
namespace RhFrequencyDilationCompact
open RhDilation RhWeightedMeasureEmbedding RhWeightedFrequencyDensity

lemma pointwise_dilate_tendsto {r : ℕ → ℝ} (hr : Tendsto r atTop (𝓝 1))
    {g : ℝ → ℂ} (hg : Continuous g) (xi : ℝ) :
    Tendsto (fun n => complexDilate (r n) g xi) atTop (𝓝 (g xi)) := by
  have hs : Tendsto (fun n => Real.sqrt (r n)) atTop (𝓝 1) := by
    simpa only [Real.sqrt_one, Function.comp_def] using Real.continuous_sqrt.continuousAt.tendsto.comp hr
  have hi : Tendsto (fun n => (Real.sqrt (r n))⁻¹) atTop (𝓝 1) := by
    simpa only [inv_one] using hs.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
  have hx : Tendsto (fun n => xi / r n) atTop (𝓝 xi) := by
    have ht := (tendsto_const_nhds : Tendsto (fun _ : ℕ => xi) atTop (𝓝 xi)).div
      hr (by norm_num : (1 : ℝ) ≠ 0)
    change Tendsto (fun n => xi / r n) atTop (𝓝 (xi / 1)) at ht
    simpa only [div_one] using ht
  have hcomplex := (Complex.continuous_ofReal.continuousAt.tendsto.comp hi).mul
    (hg.continuousAt.tendsto.comp hx)
  simpa only [Function.comp_def, Complex.ofReal_one, one_mul, complexDilate] using hcomplex

/-- A genuine weighted square-error integral limit for each actual compact
continuous frequency function. Native weighted local finiteness is proved. -/
theorem compact_square_error_tendsto {r : ℕ → ℝ}
    (hr1 : ∀ n, 1 ≤ r n) (hr2 : ∀ n, r n ≤ 2) (hr : Tendsto r atTop (𝓝 1))
    {g : ℝ → ℂ} (hg : Continuous g) (hc : HasCompactSupport g) :
    Tendsto (fun n => ∫ xi, ‖complexDilate (r n) g xi - g xi‖ ^ 2 ∂weightedMeasure)
      atTop (𝓝 0) := by
  obtain ⟨B, hB, hsub⟩ := hc.isBounded.subset_closedBall_lt 0 (0 : ℝ)
  obtain ⟨M, hM⟩ := hc.isCompact.exists_bound_of_continuousOn hg.continuousOn
  let D : ℝ := max M 0 + 1
  have hD : 0 < D := by dsimp [D]; positivity
  have hgB (xi : ℝ) : ‖g xi‖ ≤ D := by
    by_cases ht : xi ∈ tsupport g
    · exact (hM xi ht).trans (by dsimp [D]; linarith [le_max_left M 0])
    · have hz : g xi = 0 := by
        by_contra hn
        exact ht (subset_tsupport g hn)
      rw [hz, norm_zero]
      exact hD.le
  have hz (xi : ℝ) (hxi : xi ∉ Icc (-B) B) : g xi = 0 := by
    by_contra hn
    have ht := hsub (subset_tsupport g hn)
    have hnorm : |xi| ≤ B := by
      simpa only [Metric.mem_closedBall, Real.dist_eq, sub_zero] using ht
    exact hxi (abs_le.mp hnorm)
  let box : Set ℝ := Icc (-(2 * B)) (2 * B)
  let bound : ℝ → ℝ := box.indicator (fun _ => 4 * D ^ 2)
  have hi : Integrable bound weightedMeasure :=
    (integrable_indicator_iff measurableSet_Icc).mpr
      (integrableOn_const isCompact_Icc.measure_ne_top)
  have hmeas (n : ℕ) : AEStronglyMeasurable
      (fun xi => ‖complexDilate (r n) g xi - g xi‖ ^ 2) weightedMeasure := by
    have hcd : Continuous (complexDilate (r n) g) := by
      unfold complexDilate
      exact continuous_const.mul (hg.comp (continuous_id.div_const (r n)))
    exact ((hcd.sub hg).norm.pow 2).aestronglyMeasurable
  have hbound (n : ℕ) : ∀ᵐ xi ∂weightedMeasure,
      ‖‖complexDilate (r n) g xi - g xi‖ ^ 2‖ ≤ bound xi := by
    apply Eventually.of_forall
    intro xi
    have hr0 : 0 < r n := by linarith [hr1 n]
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    by_cases ht : xi ∈ box
    · rw [show bound xi = 4 * D ^ 2 from indicator_of_mem ht _]
      have hscaled : ‖complexDilate (r n) g xi‖ ≤ D := by
        simp only [complexDilate, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))]
        have hs : (Real.sqrt (r n))⁻¹ ≤ 1 :=
          inv_le_one_of_one_le₀ (Real.one_le_sqrt.mpr (hr1 n))
        calc
          _ ≤ 1 * ‖g (xi / r n)‖ := mul_le_mul_of_nonneg_right hs (norm_nonneg _)
          _ ≤ D := by simpa only [one_mul] using hgB (xi / r n)
      have hn := norm_sub_le (complexDilate (r n) g xi) (g xi)
      have hh := hgB xi
      nlinarith [norm_nonneg (complexDilate (r n) g xi - g xi)]
    · have hxi : xi ∉ Icc (-B) B := by
        intro hin
        apply ht
        exact ⟨by linarith [hin.1], by linarith [hin.2]⟩
      have hscaled : xi / r n ∉ Icc (-B) B := by
        intro hin
        have hout := (RhDilation.mem_interval_div_iff hr0 B xi).mp hin
        apply ht
        change -(2 * B) ≤ xi ∧ xi ≤ 2 * B
        have hm : r n * B ≤ 2 * B := mul_le_mul_of_nonneg_right (hr2 n) hB.le
        constructor <;> linarith [hout.1, hout.2]
      simp [bound, ht, complexDilate, hz xi hxi, hz (xi / r n) hscaled]
  have hlim : ∀ᵐ xi ∂weightedMeasure, Tendsto
      (fun n => ‖complexDilate (r n) g xi - g xi‖ ^ 2) atTop (𝓝 (0 : ℝ)) := by
    apply Eventually.of_forall
    intro xi
    simpa only [sub_self, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0)] using
      ((pointwise_dilate_tendsto hr hg xi).sub_const (g xi)).norm.pow 2
  simpa only [integral_zero] using
    tendsto_integral_of_dominated_convergence bound hmeas hi hbound hlim

end RhFrequencyDilationCompact
#print axioms RhFrequencyDilationCompact.pointwise_dilate_tendsto
#print axioms RhFrequencyDilationCompact.compact_square_error_tendsto
