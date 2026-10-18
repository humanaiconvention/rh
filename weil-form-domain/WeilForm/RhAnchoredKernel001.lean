import RhAnchoredSpace001
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.MetricSpace.Lipschitz

set_option maxHeartbeats 0
noncomputable section
open MeasureTheory Set Filter
open scoped Topology Interval BigOperators
namespace RhAnchored

lemma abs_lipschitz : LipschitzWith 1 (fun x : ℝ => |x|) := by
  apply LipschitzWith.mk_one
  intro x y
  simpa only [Real.dist_eq] using abs_abs_sub_abs_le_abs_sub x y

lemma positivePart_lipschitz : LipschitzWith 1 (fun x : ℝ => max x 0) := by
  simpa using (LipschitzWith.id.max (LipschitzWith.const (0 : ℝ)))

lemma exp_nonpositive_lipschitz : LipschitzOnWith 1 Real.exp (Iic 0) := by
  apply (convex_Iic (0 : ℝ)).lipschitzOnWith_of_nnnorm_deriv_le
  · intro x _
    exact Real.differentiableAt_exp
  · intro x hx
    change ‖deriv Real.exp x‖ ≤ (1 : ℝ)
    simpa only [Real.deriv_exp, Real.norm_eq_abs, abs_of_pos (Real.exp_pos x)] using
      (Real.exp_le_one_iff.mpr hx)

lemma affine_ac (m c a b : ℝ) :
    AbsolutelyContinuousOnInterval (fun x => c+m*x) a b := by
  apply ContDiffOn.absolutelyContinuousOnInterval
  fun_prop

lemma abs_affine_ac (m c a b : ℝ) :
    AbsolutelyContinuousOnInterval (fun x => |c+m*x|) a b := by
  exact abs_lipschitz.comp_absolutelyContinuousOnInterval (affine_ac m c a b)

lemma exp_abs_affine_ac {ν : ℝ} (hν : 0 ≤ ν) (m c a b : ℝ) :
    AbsolutelyContinuousOnInterval (fun x => Real.exp (-ν*|c+m*x|)) a b := by
  apply exp_nonpositive_lipschitz.comp_absolutelyContinuousOnInterval
  · intro x _
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hν) (abs_nonneg _)
  · exact (abs_affine_ac m c a b).const_mul (-ν)

lemma finite_sum_ac {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℝ) (a b : ℝ)
    (hf : ∀ i ∈ s, AbsolutelyContinuousOnInterval (f i) a b) :
    AbsolutelyContinuousOnInterval (fun x => ∑ i ∈ s, f i x) a b := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    apply ContDiffOn.absolutelyContinuousOnInterval
    fun_prop
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (hf i (by simp)).fun_add (ih (fun j hj => hf j (by simp [hj])))

lemma beta_pos (k : ℕ) : 0 < beta k := by
  unfold beta archIndex
  positivity

lemma finitePotential_ac_affine (C α L : ℝ) (J : ℕ) (m c a b : ℝ) :
    AbsolutelyContinuousOnInterval (fun x => finitePotential C α L J (c+m*x)) a b := by
  have hcosh : AbsolutelyContinuousOnInterval
      (fun x => -8*(Real.cosh ((c+m*x)/2)-1)) a b := by
    apply ContDiffOn.absolutelyContinuousOnInterval
    fun_prop
  have habs := (abs_affine_ac m c a b).const_mul (C/2)
  have hexp : AbsolutelyContinuousOnInterval
      (fun x => ∑ k ∈ Finset.range J,
        (1-Real.exp (-(beta k)*|c+m*x|))/(4*(archIndex k)^2)) a b := by
    apply finite_sum_ac
    intro k _
    have hconst : AbsolutelyContinuousOnInterval (fun _ : ℝ => (1 : ℝ)) a b := by
      apply ContDiffOn.absolutelyContinuousOnInterval
      fun_prop
    have hs := (hconst.sub (exp_abs_affine_ac (beta_pos k).le m c a b)).const_mul
      ((4*(archIndex k)^2)⁻¹)
    convert hs using 1
    ext x
    simp only [Pi.sub_apply, div_eq_mul_inv]
    ring
  have hhinge : AbsolutelyContinuousOnInterval
      (fun x => α*max (|c+m*x|-L) 0) a b := by
    have hconst : AbsolutelyContinuousOnInterval (fun _ : ℝ => L) a b := by
      apply ContDiffOn.absolutelyContinuousOnInterval
      fun_prop
    exact (positivePart_lipschitz.comp_absolutelyContinuousOnInterval
      ((abs_affine_ac m c a b).sub hconst)).const_mul α
  exact ((hcosh.fun_add habs).fun_sub hexp).fun_add hhinge

lemma finiteKernel_section_ac (C α L : ℝ) (J : ℕ) (t a b : ℝ) :
    AbsolutelyContinuousOnInterval (fun u => finiteKernel C α L J t u) a b := by
  have h1 := finitePotential_ac_affine C α L J (-1) t a b
  have h2 := finitePotential_ac_affine C α L J (-1) 0 a b
  have hc1 : AbsolutelyContinuousOnInterval
      (fun _ : ℝ => finitePotential C α L J t) a b := by
    apply ContDiffOn.absolutelyContinuousOnInterval
    fun_prop
  have hc0 : AbsolutelyContinuousOnInterval
      (fun _ : ℝ => finitePotential C α L J 0) a b := by
    apply ContDiffOn.absolutelyContinuousOnInterval
    fun_prop
  simpa only [finiteKernel, anchoredKernel, neg_one_mul, zero_add, sub_eq_add_neg]
    using ((h1.fun_sub hc1).fun_sub h2).fun_add hc0

theorem finiteKernel_first_parts {A : ℝ} (hA : 0 < A) {v : ℝ → ℝ}
    (hv : MemLp v 2 (physicalMeasure A)) (C α L : ℝ) (J : ℕ) (t : ℝ) :
    (∫ u in interval A, finiteKernel C α L J t u * v u) =
    -(∫ u in interval A, primitive A v u *
      deriv (fun y => finiteKernel C α L J t y) u) := by
  have h := primitive_parts_setIntegral_anchored hA hv
    (finiteKernel_section_ac C α L J t (-A) A) (finiteKernel_zero_right C α L J t)
  simpa only [mul_comm] using h

def archConstant : ℝ := Real.eulerMascheroniConstant+Real.pi/2+3*Real.log 2+Real.log Real.pi
def firstPrimeLog : ℝ := Real.log 2
def firstPrimeWeight : ℝ := Real.log 2 / Real.sqrt 2
def nativeDiagonal (C : ℝ) (J : ℕ) : ℝ := (∑ k ∈ Finset.range J, (archIndex k)⁻¹)-C
def exponentialOperator (A ν : ℝ) (w : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ u in interval A, Real.exp (-ν*|t-u|)*w u
def primeShift (A L : ℝ) (w : ℝ → ℝ) (t : ℝ) : ℝ :=
  zeroExtension A w (t+L)+zeroExtension A w (t-L)
def nativeOperator (A C α L : ℝ) (J : ℕ) (w : ℝ → ℝ) (t : ℝ) : ℝ :=
  nativeDiagonal C J*w t
  + 2*Real.cosh (t/2)*(∫ u in interval A, Real.cosh (u/2)*w u)
  - 2*Real.sinh (t/2)*(∫ u in interval A, Real.sinh (u/2)*w u)
  - ∑ k ∈ Finset.range J, exponentialOperator A (beta k) w t
  - α*primeShift A L w t

end RhAnchored
#print axioms RhAnchored.finiteKernel_section_ac
#print axioms RhAnchored.finiteKernel_first_parts
