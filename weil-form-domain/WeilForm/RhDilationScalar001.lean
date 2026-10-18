import RhDilationScalarHead001
import Mathlib.Analysis.Calculus.Deriv.MeanValue

noncomputable section
open Set Filter
open scoped Topology BigOperators

namespace RhDilationScalar

open RhTail

def finitePath (b ω : ℝ) (K : ℕ) (t : ℝ) : ℝ :=
  ∑ k ∈ Finset.range K, multiplier ((ω * Real.exp t) ^ 2) (b + 2 * k)

lemma multiplier_first_hasDerivAt {x s : ℝ} (hx : 0 ≤ x) (hs : 0 < s) :
    HasDerivAt (fun y : ℝ => multiplier y s) (2 * s / (s ^ 2 + x) ^ 2) x := by
  have hden : s * (s ^ 2 + x) ≠ 0 := ne_of_gt (by positivity)
  have hh := ((hasDerivAt_id x).const_mul 2).div
    (((hasDerivAt_id x).const_add (s ^ 2)).const_mul s) hden
  convert hh using 1
  · rfl
  · simp only [id_eq, mul_one, one_mul]
    field_simp
    <;> ring

lemma multiplier_path_hasDerivAt {b : ℝ} (hb : 0 < b) (ω t : ℝ) :
    HasDerivAt (fun y : ℝ => multiplier ((ω * Real.exp y) ^ 2) b)
      (scaleDerivative ((ω * Real.exp t) ^ 2) b) t := by
  have hx := ((Real.hasDerivAt_exp t).const_mul ω).pow 2
  have hh := (multiplier_first_hasDerivAt (sq_nonneg (ω * Real.exp t)) hb).comp t hx
  convert hh using 1
  · rfl
  · unfold scaleDerivative
    simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
    ring

lemma finitePath_hasDerivAt {b : ℝ} (hb : 0 < b) (ω : ℝ) (K : ℕ) (t : ℝ) :
    HasDerivAt (finitePath b ω K)
      (∑ k ∈ Finset.range K, scaleDerivative ((ω * Real.exp t) ^ 2) (b + 2 * k)) t := by
  exact HasDerivAt.fun_sum (fun k _ => multiplier_path_hasDerivAt (by positivity) ω t)

lemma finitePath_deriv_bounds {b : ℝ} (hb : 0 < b) (ω : ℝ) (K : ℕ) (t : ℝ) :
    0 ≤ deriv (finitePath b ω K) t ∧
      deriv (finitePath b ω K) t ≤ 1 + 2 / b := by
  rw [(finitePath_hasDerivAt hb ω K t).deriv]
  exact ⟨Finset.sum_nonneg (fun k _ => scaleDerivative_nonneg (sq_nonneg _) (by positivity)),
    finite_scaleDerivative_bound (sq_nonneg _) hb K⟩

/-- Finite sums already have the same logarithmic dilation budget. -/
theorem finite_multiplier_scaling {b r : ℝ} (hb : 0 < b) (hr : 1 ≤ r)
    (ω : ℝ) (K : ℕ) :
    0 ≤ (∑ k ∈ Finset.range K, multiplier (ω ^ 2) (b + 2 * k)) -
      (∑ k ∈ Finset.range K, multiplier ((ω / r) ^ 2) (b + 2 * k)) ∧
    (∑ k ∈ Finset.range K, multiplier (ω ^ 2) (b + 2 * k)) -
      (∑ k ∈ Finset.range K, multiplier ((ω / r) ^ 2) (b + 2 * k)) ≤
      (1 + 2 / b) * Real.log r := by
  have hrp : 0 < r := by linarith
  have hl : 0 ≤ Real.log r := Real.log_nonneg hr
  have hf : Differentiable ℝ (finitePath b ω K) :=
    fun t => (finitePath_hasDerivAt hb ω K t).differentiableAt
  have hm := monotone_of_deriv_nonneg hf (fun t => (finitePath_deriv_bounds hb ω K t).1)
  have hu := image_sub_le_mul_sub_of_deriv_le hf
    (fun t => (finitePath_deriv_bounds hb ω K t).2) (by linarith : -Real.log r ≤ 0)
  have he0 : finitePath b ω K 0 =
      ∑ k ∈ Finset.range K, multiplier (ω ^ 2) (b + 2 * k) := by
    simp [finitePath]
  have he1 : finitePath b ω K (-Real.log r) =
      ∑ k ∈ Finset.range K, multiplier ((ω / r) ^ 2) (b + 2 * k) := by
    simp only [finitePath, Real.exp_neg, Real.exp_log hrp, div_eq_mul_inv]
  have hn := hm (by linarith : -Real.log r ≤ 0)
  rw [he0, he1] at hn hu
  constructor
  · linarith
  · simpa only [sub_neg_eq_add, zero_add] using hu

lemma multiplier_series_summable_pos {x b : ℝ} (hx : 0 ≤ x) (hb : 0 < b) :
    Summable (fun k : ℕ => multiplier x (b + 2 * k)) := by
  apply (summable_nat_add_iff 1).mp
  have ht := multiplier_series_summable hx (by linarith : 1 ≤ b + 2)
  convert ht using 1
  funext k
  congr 1
  push_cast
  ring

def archMultiplier (b ω : ℝ) : ℝ := ∑' k : ℕ, multiplier (ω ^ 2) (b + 2 * k)

/-- Actual infinite multiplier scaling: all convergence is proved from b>0. -/
theorem archMultiplier_scaling {b r : ℝ} (hb : 0 < b) (hr : 1 ≤ r) (ω : ℝ) :
    0 ≤ archMultiplier b ω - archMultiplier b (ω / r) ∧
      archMultiplier b ω - archMultiplier b (ω / r) ≤ (1 + 2 / b) * Real.log r := by
  have h0 := (multiplier_series_summable_pos (sq_nonneg ω) hb).hasSum.tendsto_sum_nat
  have h1 := (multiplier_series_summable_pos (sq_nonneg (ω / r)) hb).hasSum.tendsto_sum_nat
  have hd := h0.sub h1
  constructor
  · exact le_of_tendsto_of_tendsto tendsto_const_nhds hd
      (Eventually.of_forall (fun K => (finite_multiplier_scaling hb hr ω K).1))
  · exact le_of_tendsto_of_tendsto hd tendsto_const_nhds
      (Eventually.of_forall (fun K => (finite_multiplier_scaling hb hr ω K).2))

/-- Exact constant five at the native first archimedean frequency. -/
theorem beta_half_scaling {r : ℝ} (hr : 1 ≤ r) (ω : ℝ) :
    0 ≤ archMultiplier (1 / 2) ω - archMultiplier (1 / 2) (ω / r) ∧
      archMultiplier (1 / 2) ω - archMultiplier (1 / 2) (ω / r) ≤ 5 * Real.log r := by
  have ht := archMultiplier_scaling (by norm_num : (0 : ℝ) < 1 / 2) hr ω
  have he : (1 : ℝ) + 2 / (1 / 2) = 5 := by norm_num
  simpa only [he] using ht

end RhDilationScalar
#print axioms RhDilationScalar.finite_multiplier_scaling
#print axioms RhDilationScalar.multiplier_series_summable_pos
#print axioms RhDilationScalar.archMultiplier_scaling
#print axioms RhDilationScalar.beta_half_scaling

