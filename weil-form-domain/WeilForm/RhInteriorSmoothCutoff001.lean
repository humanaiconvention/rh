import RhSmoothPrimitiveCore001
import RhDilationRankL2001
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence

noncomputable section
open Set MeasureTheory Filter
open scoped Topology ContDiff Interval
namespace RhInteriorSmoothCutoff
open RhAnchored

def delta (R : ℝ) (n : ℕ) : ℝ := R / ((n : ℝ) + 2)
lemma delta_pos {R : ℝ} (hR : 0 < R) (n : ℕ) : 0 < delta R n := by
  unfold delta
  positivity
lemma delta_lt {R : ℝ} (hR : 0 < R) (n : ℕ) : delta R n < R := by
  unfold delta
  apply (div_lt_iff₀ (by positivity : 0 < (n : ℝ) + 2)).2
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  nlinarith

def cutoffBump (R : ℝ) (hR : 0 < R) (n : ℕ) : ContDiffBump (0 : ℝ) where
  rIn := R - delta R n
  rOut := R - delta R n / 2
  rIn_pos := by linarith [delta_lt hR n]
  rIn_lt_rOut := by linarith [delta_pos hR n]

def cutoff (R : ℝ) (hR : 0 < R) (n : ℕ) : ℝ → ℝ := cutoffBump R hR n

lemma cutoff_contDiff {R : ℝ} (hR : 0 < R) (n : ℕ) :
    ContDiff ℝ ∞ (cutoff R hR n) := (cutoffBump R hR n).contDiff
lemma cutoff_nonneg {R : ℝ} (hR : 0 < R) (n : ℕ) (t : ℝ) :
    0 ≤ cutoff R hR n t := (cutoffBump R hR n).nonneg
lemma cutoff_le_one {R : ℝ} (hR : 0 < R) (n : ℕ) (t : ℝ) :
    cutoff R hR n t ≤ 1 := (cutoffBump R hR n).le_one
lemma cutoff_hasCompactSupport {R : ℝ} (hR : 0 < R) (n : ℕ) :
    HasCompactSupport (cutoff R hR n) := (cutoffBump R hR n).hasCompactSupport
lemma cutoff_tsupport {R : ℝ} (hR : 0 < R) (n : ℕ) :
    tsupport (cutoff R hR n) ⊆ Ioo (-R) R := by
  change tsupport (cutoffBump R hR n) ⊆ Ioo (-R) R
  rw [(cutoffBump R hR n).tsupport_eq]
  intro t ht
  have htabs : |t| ≤ R - delta R n / 2 := by
    simpa only [Metric.mem_closedBall, Real.dist_eq, sub_zero, cutoffBump] using ht
  have hd := delta_pos hR n
  have ha := (abs_le.mp htabs)
  constructor <;> linarith [ha.1, ha.2]

lemma delta_tendsto (R : ℝ) : Tendsto (delta R) atTop (𝓝 0) := by
  have h := (tendsto_const_div_atTop_nhds_zero_nat R).comp (tendsto_add_atTop_nat 2)
  change Tendsto (fun n : ℕ => R / ((n : ℝ) + 2)) atTop (𝓝 0)
  simpa only [Function.comp_def, Nat.cast_add, Nat.cast_ofNat] using h

lemma cutoff_eventually_one {R t : ℝ} (hR : 0 < R) (ht : t ∈ Ioo (-R) R) :
    ∀ᶠ n in atTop, cutoff R hR n t = 1 := by
  have hgap : 0 < R - |t| := by
    have ha := abs_lt.mpr ht
    linarith
  have hd : ∀ᶠ n in atTop, delta R n < R - |t| :=
    (tendsto_order.1 (delta_tendsto R)).2 _ hgap
  filter_upwards [hd] with n hn
  apply (cutoffBump R hR n).one_of_mem_closedBall
  change dist t 0 ≤ R - delta R n
  rw [Real.dist_eq, sub_zero]
  linarith

lemma physical_ae_interior (R : ℝ) :
    ∀ᵐ t ∂physicalMeasure R, t ∈ Ioo (-R) R := by
  have hn (c : ℝ) : ∀ᵐ t ∂volume, t ≠ c := by
    have h : volume ({c} : Set ℝ) = 0 := by simp
    rw [measure_eq_zero_iff_ae_notMem] at h
    simpa only [mem_singleton_iff] using h
  unfold physicalMeasure
  rw [ae_restrict_iff' (show MeasurableSet (interval R) from measurableSet_Icc)]
  filter_upwards [hn (-R), hn R] with t hneg hpos ht
  exact ⟨lt_of_le_of_ne ht.1 (Ne.symm hneg), lt_of_le_of_ne ht.2 hpos⟩

lemma cutoff_mul_memLp {R : ℝ} (hR : 0 < R) (n : ℕ) {g : ℝ → ℝ}
    (hg : Continuous g) : MemLp (fun t => cutoff R hR n t * g t) 2 (physicalMeasure R) :=
  RhDilationRank.continuous_memLp ((cutoff_contDiff hR n).continuous.mul hg)

lemma cutoff_square_error_tendsto {R : ℝ} (hR : 0 < R) {g : ℝ → ℝ}
    (hg : Continuous g) :
    Tendsto (fun n => ∫ t in interval R, (cutoff R hR n t * g t - g t)^2)
      atTop (𝓝 0) := by
  have hi : IntegrableOn (fun t => (g t)^2) (interval R) :=
    (hg.pow 2).continuousOn.integrableOn_Icc
  have h := tendsto_integral_of_dominated_convergence
    (μ := physicalMeasure R) (fun t => (g t)^2)
    (F := fun n t => (cutoff R hR n t * g t - g t)^2) (f := fun _ => (0 : ℝ))
  change Tendsto (fun n => ∫ t : ℝ, (cutoff R hR n t * g t - g t)^2 ∂physicalMeasure R)
    atTop (𝓝 0)
  rw [← show (∫ t : ℝ, (0 : ℝ) ∂physicalMeasure R) = 0 by simp]
  apply h
  · intro n
    exact (((cutoff_contDiff hR n).continuous.mul hg).sub hg).aestronglyMeasurable.pow 2
  · exact hi
  · intro n
    exact Eventually.of_forall (fun t => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      have hc : |cutoff R hR n t - 1| ≤ 1 :=
        abs_le.mpr ⟨by linarith [cutoff_nonneg hR n t],
          by linarith [cutoff_le_one hR n t]⟩
      have he : |cutoff R hR n t * g t - g t| ≤ |g t| := by
        calc
          _ = |(cutoff R hR n t - 1) * g t| := by congr 1; ring
          _ = |cutoff R hR n t - 1| * |g t| := abs_mul _ _
          _ ≤ 1 * |g t| := mul_le_mul_of_nonneg_right hc (abs_nonneg _)
          _ = _ := one_mul _
      have hp := mul_nonneg (sub_nonneg.mpr he)
        (add_nonneg (abs_nonneg (g t)) (abs_nonneg (cutoff R hR n t * g t - g t)))
      nlinarith [sq_abs (g t), sq_abs (cutoff R hR n t * g t - g t)])
  · filter_upwards [physical_ae_interior R] with t ht
    apply tendsto_const_nhds.congr'
    filter_upwards [cutoff_eventually_one hR ht] with n hn
    simp only [hn, one_mul, sub_self, zero_pow (by decide : (2 : ℕ) ≠ 0)]

lemma cutoff_L2_error_tendsto {R : ℝ} (hR : 0 < R) {g : ℝ → ℝ}
    (hg : Continuous g) :
    Tendsto (fun n => ‖(cutoff_mul_memLp hR n hg).toLp
      (fun t => cutoff R hR n t * g t) -
      (RhDilationRank.continuous_memLp hg).toLp g‖) atTop (𝓝 0) := by
  have he (n : ℕ) :
      ‖(cutoff_mul_memLp hR n hg).toLp (fun t => cutoff R hR n t * g t) -
        (RhDilationRank.continuous_memLp hg).toLp g‖^2 =
        ∫ t in interval R, (cutoff R hR n t * g t - g t)^2 := by
    rw [← MemLp.toLp_sub, RhDilationRank.norm_sq_toLp]
    rfl
  have h := Real.continuous_sqrt.continuousAt.tendsto.comp (cutoff_square_error_tendsto hR hg)
  simp only [Real.sqrt_zero] at h
  convert h using 1
  funext n
  dsimp only [Function.comp_apply]
  rw [← he n, Real.sqrt_sq (norm_nonneg _)]

end RhInteriorSmoothCutoff
#print axioms RhInteriorSmoothCutoff.cutoff_tsupport
#print axioms RhInteriorSmoothCutoff.cutoff_eventually_one
#print axioms RhInteriorSmoothCutoff.cutoff_square_error_tendsto
#print axioms RhInteriorSmoothCutoff.cutoff_L2_error_tendsto
