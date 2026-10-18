import RhEndpointComplex001
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt

set_option maxHeartbeats 0
noncomputable section
open Set MeasureTheory Filter
open scoped Topology BigOperators
namespace RhAllPrime
open RhAnchored

/-- Exact established arithmetic coefficient; non-prime-powers have coefficient zero. -/
def weight (n : ℕ) : ℝ := ArithmeticFunction.vonMangoldt n / Real.sqrt (n:ℝ)

/-- Anchored hinge, retaining both one-variable companions and its zero value. -/
def hingeKernel (L t u : ℝ) : ℝ :=
  anchoredKernel (fun x:ℝ=>max (|x|-L) 0) t u

/-- All prime-power hinges through the declared exact integer cutoff. -/
def arithmeticKernel (N : ℕ) (t u : ℝ) : ℝ :=
  ∑n∈Finset.Icc 2 N,weight n*hingeKernel (Real.log (n:ℝ)) t u

/-- Complete archimedean series plus every arithmetic hinge through N. -/
def completeKernel (N : ℕ) (t u : ℝ) : ℝ :=
  fullKernel archConstant 0 0 t u+arithmeticKernel N t u

def radiusCutoff (R : ℝ) : ℕ := Nat.floor (Real.exp (2*R))
def radiusKernel (R t u : ℝ) : ℝ := completeKernel (radiusCutoff R) t u

lemma weight_nonneg (n : ℕ) : 0≤weight n :=
  div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _)

lemma weight_prime {p : ℕ} (hp : p.Prime) :
    weight p=Real.log (p:ℝ)/Real.sqrt (p:ℝ) := by
  rw [weight,ArithmeticFunction.vonMangoldt_apply_prime hp]

lemma weight_prime_pow {p k : ℕ} (hp : p.Prime) (hk : k≠0) :
    weight (p^k)=Real.log (p:ℝ)/Real.sqrt ((p^k:ℕ):ℝ) := by
  rw [weight,ArithmeticFunction.vonMangoldt_apply_pow hk,
    ArithmeticFunction.vonMangoldt_apply_prime hp]

lemma weight_not_prime_pow {n : ℕ} (hn : ¬IsPrimePow n) : weight n=0 := by
  rw [weight,ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hn,zero_div]

lemma weight_two : weight 2=firstPrimeWeight := by
  rw [weight_prime (by norm_num : Nat.Prime 2)]
  rfl
lemma weight_three : weight 3=Real.log 3/Real.sqrt 3 :=
  weight_prime (by norm_num : Nat.Prime 3)
lemma weight_four : weight 4=Real.log 2/2 := by
  have h := weight_prime_pow (p:=2) (k:=2) (by norm_num) (by norm_num)
  norm_num at h
  exact h

lemma hinge_zero_left (L u : ℝ) : hingeKernel L 0 u=0 :=
  anchoredKernel_zero_left _ _
lemma hinge_zero_right (L t : ℝ) : hingeKernel L t 0=0 :=
  anchoredKernel_zero_right _ _

lemma hinge_symmetric (L t u : ℝ) : hingeKernel L t u=hingeKernel L u t := by
  unfold hingeKernel anchoredKernel
  dsimp only
  rw [abs_sub_comm t u,abs_neg,abs_neg]
  ring

lemma hinge_joint_continuous (L : ℝ) :
    Continuous (fun p:ℝ×ℝ=>hingeKernel L p.1 p.2) := by
  unfold hingeKernel anchoredKernel
  fun_prop

lemma arithmetic_joint_continuous (N : ℕ) :
    Continuous (fun p:ℝ×ℝ=>arithmeticKernel N p.1 p.2) := by
  unfold arithmeticKernel
  exact continuous_finsetSum _ (fun n _=>continuous_const.mul (hinge_joint_continuous _))

lemma complete_joint_continuous (N : ℕ) :
    Continuous (fun p:ℝ×ℝ=>completeKernel N p.1 p.2) :=
  (RhEndpointComplex.fullKernel_joint_continuous archConstant 0 0).add
    (arithmetic_joint_continuous N)

lemma arithmetic_two (t u : ℝ) :
    arithmeticKernel 2 t u=weight 2*hingeKernel (Real.log 2) t u := by
  norm_num [arithmeticKernel]

lemma arithmetic_three (t u : ℝ) :
    arithmeticKernel 3 t u=arithmeticKernel 2 t u+weight 3*hingeKernel (Real.log 3) t u := by
  have hs : Finset.Icc 2 3=({2,3}:Finset ℕ) := by decide +kernel
  rw [arithmeticKernel,hs,arithmetic_two]
  norm_num

/-- Algebraic dictionary to the old single-hinge kernel, with its full series unchanged. -/
lemma single_hinge_split (C alpha L t u : ℝ) :
    fullKernel C alpha L t u=fullKernel C 0 0 t u+alpha*hingeKernel L t u := by
  unfold fullKernel finiteKernel hingeKernel anchoredKernel finitePotential
  simp only [Finset.sum_range_zero,zero_mul,sub_zero,add_zero]
  ring

lemma complete_two (t u : ℝ) :
    completeKernel 2 t u=fullKernel archConstant firstPrimeWeight firstPrimeLog t u := by
  rw [completeKernel,arithmetic_two,weight_two]
  exact (single_hinge_split archConstant firstPrimeWeight firstPrimeLog t u).symm

lemma complete_three (t u : ℝ) :
    completeKernel 3 t u=completeKernel 2 t u+
      (Real.log 3/Real.sqrt 3)*hingeKernel (Real.log 3) t u := by
  rw [completeKernel,arithmetic_three,weight_three]
  unfold completeKernel
  ring

end RhAllPrime
#print axioms RhAllPrime.weight_prime_pow
#print axioms RhAllPrime.complete_joint_continuous
#print axioms RhAllPrime.complete_two
#print axioms RhAllPrime.complete_three

