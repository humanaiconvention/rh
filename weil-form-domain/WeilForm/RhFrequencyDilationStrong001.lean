import RhWeightedFrequencyDilation001
import RhFrequencyDilationCompact001

/-! Whole native weighted strong dilation continuity from actual frequency
smooth density. Dense frequency vectors are never treated as spatially
supported inputs. The only crude bound 4 is an auxiliary local continuity
bound on 1<=r<=2; the exact five-log theorem remains unchanged. -/
set_option maxHeartbeats 0
noncomputable section
open Set MeasureTheory Filter FourierTransform
open scoped Topology ENNReal
namespace RhFrequencyDilationStrong
open RhDilation RhWeightedMeasureEmbedding RhWeightedEnergyIdentity
open RhWeightedFrequencyDensity RhWeightedFrequencyDilation
open RhFrequencyDilationCompact

lemma weighted_ae_comp_div {r : ℝ} (hr : 0 < r) {f g : ℝ → ℂ}
    (h : f =ᵐ[weightedMeasure] g) :
    (fun xi => f (xi / r)) =ᵐ[weightedMeasure] fun xi => g (xi / r) := by
  have hv := (Measure.absolutelyContinuous_of_le volume_le_weightedMeasure).ae_eq h
  exact (withDensity_absolutelyContinuous volume archWeight).ae_eq
    (RhWeightedDilation.ae_comp_div hr hv)

lemma weighted_dilate_congr_ae {r : ℝ} (hr : 0 < r) {f g : ℝ → ℂ}
    (h : f =ᵐ[weightedMeasure] g) :
    complexDilate r f =ᵐ[weightedMeasure] complexDilate r g := by
  filter_upwards [weighted_ae_comp_div hr h] with xi hxi
  simp only [complexDilate, hxi]

lemma frequencyDilate_sub {r : ℝ} (hr : 1 ≤ r) (F G : WeightedSpace) :
    frequencyDilate hr (F - G) = frequencyDilate hr F - frequencyDilate hr G := by
  apply Lp.ext
  filter_upwards [frequencyDilate_ae hr (F - G), frequencyDilate_ae hr F,
    frequencyDilate_ae hr G, Lp.coeFn_sub (frequencyDilate hr F) (frequencyDilate hr G),
    weighted_ae_comp_div (by linarith : 0 < r) (Lp.coeFn_sub F G)]
      with xi hsource hf hg htarget hin
  rw [hsource, htarget]
  dsimp only [Pi.sub_apply]
  rw [hf, hg]
  simp only [complexDilate, hin, Pi.sub_apply]
  ring

lemma frequencyDilate_norm_le_four {r : ℝ} (hr : 1 ≤ r) (hr2 : r ≤ 2) (F : WeightedSpace) :
    ‖frequencyDilate hr F‖ ≤ 4 * ‖F‖ := by
  have hl := Real.log_le_sub_one_of_pos (by linarith : 0 < r)
  have hs := frequencyDilate_norm_square_le hr F
  have hc : 1 + 5 * Real.log r ≤ 16 := by linarith
  have hsq : ‖frequencyDilate hr F‖ ^ 2 ≤ 16 * ‖F‖ ^ 2 :=
    hs.trans (mul_le_mul_of_nonneg_right hc (sq_nonneg _))
  nlinarith [norm_nonneg (frequencyDilate hr F), norm_nonneg F]

lemma compact_vector_norm_tendsto {r : ℕ → ℝ}
    (hr1 : ∀ n, 1 ≤ r n) (hr2 : ∀ n, r n ≤ 2) (hr : Tendsto r atTop (𝓝 1))
    (F : WeightedSpace) {g : ℝ → ℂ} (hg : Continuous g) (hc : HasCompactSupport g)
    (hfg : F =ᵐ[weightedMeasure] g) :
    Tendsto (fun n => ‖frequencyDilate (hr1 n) F - F‖) atTop (𝓝 0) := by
  have he (n : ℕ) : ‖frequencyDilate (hr1 n) F - F‖ ^ 2 =
      ∫ xi, ‖complexDilate (r n) g xi - g xi‖ ^ 2 ∂weightedMeasure := by
    rw [lp_norm_sq_integral]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (frequencyDilate (hr1 n) F) F,
      frequencyDilate_ae (hr1 n) F, hfg,
      weighted_dilate_congr_ae (by linarith [hr1 n] : 0 < r n) hfg]
      with xi hsub hd hf hscaled
    rw [hsub]
    dsimp only [Pi.sub_apply]
    rw [hd, hf, hscaled]
  have hsq : Tendsto (fun n => ‖frequencyDilate (hr1 n) F - F‖ ^ 2) atTop (𝓝 0) := by
    simpa only [he] using compact_square_error_tendsto hr1 hr2 hr hg hc
  have hs := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using hs

/-- Strong complete weighted convergence for EVERY native weighted vector.
The result is not restricted to the actual physical primitive subclass. -/
theorem frequencyDilate_norm_tendsto {r : ℕ → ℝ}
    (hr1 : ∀ n, 1 ≤ r n) (hr2 : ∀ n, r n ≤ 2) (hr : Tendsto r atTop (𝓝 1))
    (F : WeightedSpace) :
    Tendsto (fun n => ‖frequencyDilate (hr1 n) F - F‖) atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.mpr
  intro epsilon hepsilon
  obtain ⟨G, hG, hclose⟩ := frequency_smooth_dense.exists_dist_lt F
    (show 0 < epsilon / 12 by positivity)
  obtain ⟨g, hfg, hgC, hgS⟩ := hG
  have hG0 := compact_vector_norm_tendsto hr1 hr2 hr G hgS.continuous hgC hfg
  have hsmall : ∀ᶠ n in atTop, ‖frequencyDilate (hr1 n) G - G‖ < epsilon / 2 :=
    (tendsto_order.mp hG0).2 _ (by positivity)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hsmall
  refine ⟨N, ?_⟩
  intro n hn
  rw [Real.dist_eq, sub_zero, abs_norm]
  have hFG : ‖F - G‖ < epsilon / 12 := by simpa only [dist_eq_norm] using hclose
  have hGF : ‖G - F‖ = ‖F - G‖ := norm_sub_rev _ _
  have he : frequencyDilate (hr1 n) F - F =
      frequencyDilate (hr1 n) (F - G) + (frequencyDilate (hr1 n) G - G) + (G - F) := by
    rw [frequencyDilate_sub]
    abel
  have hbound : ‖frequencyDilate (hr1 n) F - F‖ ≤
      4 * ‖F - G‖ + ‖frequencyDilate (hr1 n) G - G‖ + ‖G - F‖ := by
    rw [he]
    have h1 := norm_add_le (frequencyDilate (hr1 n) (F - G))
      (frequencyDilate (hr1 n) G - G)
    have h2 := norm_add_le (frequencyDilate (hr1 n) (F - G) +
      (frequencyDilate (hr1 n) G - G)) (G - F)
    have h3 := frequencyDilate_norm_le_four (hr1 n) (hr2 n) (F - G)
    linarith
  rw [hGF] at hbound
  linarith [hN n hn]

end RhFrequencyDilationStrong
#print axioms RhFrequencyDilationStrong.frequencyDilate_sub
#print axioms RhFrequencyDilationStrong.compact_vector_norm_tendsto
#print axioms RhFrequencyDilationStrong.frequencyDilate_norm_tendsto
