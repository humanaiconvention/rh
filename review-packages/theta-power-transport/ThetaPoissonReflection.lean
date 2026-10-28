import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Tactic

/-!
Actual real Gaussian Poisson reflection and exact derivative parity.
The recorded bounded build owns acceptance. No actual theta symmetry is
assumed: reflection below follows from the real Gaussian Poisson identity.
-/

noncomputable section
open scoped BigOperators

namespace ThetaMacdonald.Reflection

def fullTheta (u : ℝ) : ℝ :=
  ∑' n : ℤ, Real.exp (-Real.pi * Real.exp (2 * u) * (n : ℝ)^2)

def centeredFullTheta (u : ℝ) : ℝ :=
  Real.exp (u / 2) * fullTheta u

theorem exp_half_rpow (u : ℝ) :
    Real.exp (2 * u) ^ (1 / 2 : ℝ) = Real.exp u := by
  rw [← Real.exp_mul]
  congr 1
  ring

theorem fullTheta_poisson (u : ℝ) :
    fullTheta u = Real.exp (-u) * fullTheta (-u) := by
  have h := Real.tsum_exp_neg_mul_int_sq
    (a := Real.exp (2 * u)) (Real.exp_pos (2 * u))
  rw [exp_half_rpow, one_div, ← Real.exp_neg] at h
  have hphase : ∀ n : ℤ,
      Real.exp (-Real.pi / Real.exp (2 * u) * (n : ℝ)^2) =
        Real.exp (-Real.pi * Real.exp (2 * (-u)) * (n : ℝ)^2) := by
    intro n
    rw [show 2 * (-u) = -(2 * u) by ring, Real.exp_neg,
      div_eq_mul_inv]
  change fullTheta u = Real.exp (-u) * _ at h
  simpa only [hphase, fullTheta] using h

theorem centeredFullTheta_even (u : ℝ) :
    centeredFullTheta (-u) = centeredFullTheta u := by
  unfold centeredFullTheta
  rw [fullTheta_poisson u, ← mul_assoc, ← Real.exp_add]
  congr 1
  congr 1
  ring

/-- An exact derivative parity transport, without an extra third derivative
series interchange. Derivatives are Lean's total derivative. -/
theorem deriv_odd_of_even {f : ℝ → ℝ}
    (hf : ∀ x, f (-x) = f x) (x : ℝ) :
    deriv f (-x) = -deriv f x := by
  have heq : (fun t : ℝ => f (-t)) = f := funext hf
  have hd := congrArg (fun g : ℝ → ℝ => deriv g x) heq
  rw [deriv_comp_neg] at hd
  linarith

theorem second_deriv_even_of_even {f : ℝ → ℝ}
    (hf : ∀ x, f (-x) = f x) (x : ℝ) :
    deriv (deriv f) (-x) = deriv (deriv f) x := by
  have heq : (fun t : ℝ => deriv f (-t)) =
      fun t : ℝ => -deriv f t :=
    funext (deriv_odd_of_even hf)
  have hd := congrArg (fun g : ℝ → ℝ => deriv g x) heq
  rw [deriv_comp_neg, deriv.fun_neg] at hd
  linarith

theorem deriv_zero_of_even {f : ℝ → ℝ}
    (hf : ∀ x, f (-x) = f x) : deriv f 0 = 0 := by
  have h := deriv_odd_of_even hf 0
  simp only [neg_zero] at h
  linarith

theorem centeredFullTheta_second_deriv_even (u : ℝ) :
    deriv (deriv centeredFullTheta) (-u) =
      deriv (deriv centeredFullTheta) u :=
  second_deriv_even_of_even centeredFullTheta_even u

theorem centeredFullTheta_deriv_zero :
    deriv centeredFullTheta 0 = 0 :=
  deriv_zero_of_even centeredFullTheta_even

end ThetaMacdonald.Reflection

#print axioms ThetaMacdonald.Reflection.centeredFullTheta_even
#print axioms ThetaMacdonald.Reflection.centeredFullTheta_second_deriv_even
#print axioms ThetaMacdonald.Reflection.centeredFullTheta_deriv_zero

