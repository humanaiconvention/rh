import RhFourierTailScalar001
import Mathlib.Analysis.PSeries

noncomputable section
open Set MeasureTheory Filter
open scoped Topology Interval BigOperators
namespace RhTail

lemma multiplier_antitone {x : ℝ} (hx : 0 ≤ x) :
    AntitoneOn (multiplier x) (Ioi 0) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ioi 0)
  · intro b hb
    exact (multiplier_hasDerivAt hx hb).continuousAt.continuousWithinAt
  · intro b hb
    exact (multiplier_hasDerivAt hx (interior_subset hb)).differentiableAt.differentiableWithinAt
  · intro b hb
    have hb' : 0 < b := interior_subset hb
    rw [(multiplier_hasDerivAt hx hb').deriv]
    unfold multiplierPrime
    apply div_nonpos_of_nonpos_of_nonneg
    · exact mul_nonpos_of_nonpos_of_nonneg (by nlinarith) (by positivity)
    · positivity

def cellChord (f : ℝ → ℝ) (b t : ℝ) : ℝ :=
  ((b+2-t)/2)*f b+((t-b)/2)*f (b+2)

lemma cellChord_integral (f : ℝ → ℝ) (b : ℝ) :
    (∫ t in b..(b+2), cellChord f b t)=f b+f (b+2) := by
  unfold cellChord
  rw [intervalIntegral.integral_add
    ((by fun_prop : Continuous (fun t : ℝ => ((b+2-t)/2)*f b)).intervalIntegrable b (b+2))
    ((by fun_prop : Continuous (fun t : ℝ => ((t-b)/2)*f (b+2))).intervalIntegrable b (b+2))]
  rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_mul_const,
    intervalIntegral.integral_div, intervalIntegral.integral_div]
  have hsub1 := intervalIntegral.integral_sub
    (μ := volume) (f := fun _ : ℝ => b+2) (g := fun t : ℝ => t)
    (continuous_const.intervalIntegrable b (b+2)) (continuous_id.intervalIntegrable b (b+2))
  have hsub2 := intervalIntegral.integral_sub
    (μ := volume) (f := fun t : ℝ => t) (g := fun _ : ℝ => b)
    (continuous_id.intervalIntegrable b (b+2)) (continuous_const.intervalIntegrable b (b+2))
  rw [hsub1, hsub2]
  simp only [intervalIntegral.integral_const, integral_id, smul_eq_mul]
  ring

lemma multiplier_cell_trapezoid {x b : ℝ} (hx : 0 ≤ x) (hb : 0 < b) :
    (∫ t in b..(b+2), multiplier x t) ≤ multiplier x b+multiplier x (b+2) := by
  have hf : ContinuousOn (multiplier x) (Icc b (b+2)) := by
    intro t ht
    exact (multiplier_hasDerivAt hx (lt_of_lt_of_le hb ht.1)).continuousAt.continuousWithinAt
  have hch : Continuous (cellChord (multiplier x) b) := by unfold cellChord; fun_prop
  rw [← cellChord_integral (multiplier x) b]
  apply intervalIntegral.integral_mono_on (by linarith : b ≤ b+2)
    (hf.intervalIntegrable_of_Icc (by linarith)) (hch.intervalIntegrable b (b+2))
  intro t ht
  have ha : 0 ≤ (b+2-t)/2 := by linarith [ht.2]
  have hc : 0 ≤ (t-b)/2 := by linarith [ht.1]
  have hab : (b+2-t)/2+(t-b)/2=(1 : ℝ) := by ring
  have h := (multiplier_convex hx).2 hb (by linarith : 0 < b+2) ha hc hab
  have he : (b+2-t)/2*b+(t-b)/2*(b+2)=t := by ring
  simpa only [smul_eq_mul, he, cellChord] using h

lemma negativeLog_hasDerivAt {x b : ℝ} (hx : 0 ≤ x) (hb : 0 < b) :
    HasDerivAt (fun t : ℝ => -Real.log (1+x/t^2)) (multiplier x b) b := by
  have hd := (hasDerivAt_const b x).div ((hasDerivAt_id b).pow 2)
    (pow_ne_zero 2 (ne_of_gt hb))
  have hp : 1+x/b^2 ≠ 0 := ne_of_gt (by positivity : 0 < 1+x/b^2)
  have h := ((hd.const_add 1).log hp).neg
  convert h using 1
  · rfl
  · unfold multiplier
    simp only [Pi.div_apply, Pi.pow_apply, id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one]
    field_simp
    <;> ring

lemma multiplier_integral {x b B : ℝ} (hx : 0 ≤ x) (hb : 0 < b) (hB : b ≤ B) :
    (∫ t in b..B, multiplier x t)=Real.log (1+x/b^2)-Real.log (1+x/B^2) := by
  have hf : ContinuousOn (multiplier x) (Icc b B) := by
    intro t ht
    exact (multiplier_hasDerivAt hx (lt_of_lt_of_le hb ht.1)).continuousAt.continuousWithinAt
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := b) (b := B) (fun t ht => negativeLog_hasDerivAt hx (by
      rw [uIcc_of_le hB] at ht
      exact lt_of_lt_of_le hb ht.1)) (hf.intervalIntegrable_of_Icc hB)
  simpa only [neg_sub_neg] using h

lemma log_cell_trapezoid {x b : ℝ} (hx : 0 ≤ x) (hb : 0 < b) :
    Real.log (1+x/b^2)-Real.log (1+x/(b+2)^2) ≤
      multiplier x b+multiplier x (b+2) := by
  rw [← multiplier_integral hx hb (by linarith : b ≤ b+2)]
  exact multiplier_cell_trapezoid hx hb

theorem finite_tail_trapezoid {x b : ℝ} (hx : 0 ≤ x) (hb : 0 < b) (K : ℕ) :
    (1/2)*(Real.log (1+x/b^2)-Real.log (1+x/(b+2*K)^2))+
      (multiplier x b-multiplier x (b+2*K))/2 ≤
      ∑ k ∈ Finset.range K, multiplier x (b+2*k) := by
  induction K with
  | zero => simp
  | succ K ih =>
    have ht : 0 < b+2*(K : ℝ) := by positivity
    have hc := log_cell_trapezoid hx ht
    rw [Finset.sum_range_succ]
    push_cast
    have he : b+2*((K : ℝ)+1)=b+2*K+2 := by ring
    rw [he]
    linarith

end RhTail
#print axioms RhTail.multiplier_antitone
#print axioms RhTail.finite_tail_trapezoid
