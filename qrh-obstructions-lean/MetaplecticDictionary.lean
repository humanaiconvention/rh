module

public import Mathlib

/-!
# Algebraic survival of the conjugate norm-157 slot

This file proves only the finite algebraic implication from the stated
unit-phase cube relation. It does not identify a particular Gauss sum
with the phase or formalize a trace formula or an analytic estimate.

The concrete Eisenstein ring is Z[omega] inside C. The phase theorem
holds for every cubic root of conjugate(alpha)^2; no branch is assumed.
-/

@[expose] public section

noncomputable section

namespace MetaplecticDictionary

open Complex
open scoped ComplexConjugate

set_option autoImplicit false

/-- The upper-half-plane primitive cube root of unity. -/
def omega : ℂ := ⟨-1 / 2, Real.sqrt 3 / 2⟩

theorem omega_quadratic : omega ^ 2 + omega + 1 = 0 := by
  have hs : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  apply Complex.ext <;> simp [omega, pow_two, Complex.mul_re, Complex.mul_im] <;>
    nlinarith

theorem omega_cube : omega ^ 3 = 1 := by
  calc
    omega ^ 3 = (omega - 1) * (omega ^ 2 + omega + 1) + 1 := by ring
    _ = 1 := by rw [omega_quadratic]; ring

theorem omega_primitive : IsPrimitiveRoot omega 3 := by
  apply IsPrimitiveRoot.mk_of_lt omega (by norm_num) omega_cube
  intro n hn hlt heq
  interval_cases n
  · have h := congrArg Complex.re heq
    norm_num [omega] at h
  · have h := congrArg Complex.re heq
    have hs : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    simp [omega, pow_two, Complex.mul_re] at h
    nlinarith

theorem omega_cyclotomic :
    Polynomial.aeval omega (Polynomial.cyclotomic 3 ℤ) = 0 := by
  simpa [Polynomial.cyclotomic_three] using omega_quadratic

theorem omega_integral : IsIntegral ℤ omega :=
  ⟨Polynomial.cyclotomic 3 ℤ, Polynomial.cyclotomic.monic 3 ℤ, omega_cyclotomic⟩

/-- The concrete subring Z[omega], regarded as a Z-subalgebra of C. -/
abbrev Eisenstein := Algebra.adjoin ℤ ({omega} : Set ℂ)

def omegaInteger : Eisenstein :=
  ⟨omega, Algebra.subset_adjoin (Set.mem_singleton omega)⟩

theorem omegaInteger_quadratic :
    omegaInteger ^ 2 + omegaInteger + 1 = 0 := by
  apply Subtype.ext
  exact omega_quadratic

def p : Eisenstein := 13 + 12 * omegaInteger
def pbar : Eisenstein := 1 - 12 * omegaInteger

theorem p_value : (p : ℂ) = ⟨7, 6 * Real.sqrt 3⟩ := by
  change (13 : ℂ) + 12 * omega = _
  apply Complex.ext <;> norm_num [omega]
  ring

theorem pbar_value : (pbar : ℂ) = ⟨7, -6 * Real.sqrt 3⟩ := by
  change (1 : ℂ) - 12 * omega = _
  apply Complex.ext <;> norm_num [omega]
  ring

theorem pbar_is_conjugate : (pbar : ℂ) = conj (p : ℂ) := by
  rw [p_value, pbar_value]
  apply Complex.ext <;> simp

theorem p_normSq : Complex.normSq (p : ℂ) = 157 := by
  rw [p_value, Complex.normSq_apply]
  have hs : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  norm_num
  nlinarith

theorem pbar_normSq : Complex.normSq (pbar : ℂ) = 157 := by
  rw [pbar_is_conjugate, Complex.normSq_conj, p_normSq]

theorem p_norm : ‖(p : ℂ)‖ = Real.sqrt 157 := by
  rw [Complex.norm_def, p_normSq]

theorem pbar_norm : ‖(pbar : ℂ)‖ = Real.sqrt 157 := by
  rw [pbar_is_conjugate, Complex.norm_conj, p_norm]

theorem p_square : (p : ℂ) ^ 2 = -59 + 84 * (Real.sqrt 3 : ℂ) * I := by
  rw [p_value]
  have hs : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  apply Complex.ext <;> simp [pow_two, Complex.mul_re, Complex.mul_im] <;>
    nlinarith

/-- The normalized generator; the denominator is positive and nonzero. -/
def alpha : ℂ := (p : ℂ) / (Real.sqrt 157 : ℂ)

theorem alpha_unit : ‖alpha‖ = 1 := by
  have hs : 0 < Real.sqrt 157 := Real.sqrt_pos.2 (by norm_num)
  simp [alpha, p_norm, abs_of_pos hs, ne_of_gt hs]

theorem alpha_square : alpha ^ 2 = (p : ℂ) ^ 2 / 157 := by
  simp only [alpha, div_pow, ← Complex.ofReal_pow]
  norm_num [Real.sq_sqrt]

theorem cube_target_sum : (conj alpha) ^ 2 + alpha ^ 2 = -(118 / 157 : ℂ) := by
  rw [← map_pow, alpha_square, map_div₀, p_square]
  apply Complex.ext <;> norm_num [Complex.div_re, Complex.div_im]
  ring

/-- A cubic root exists, and its norm is forced to be one. -/
theorem phase_exists : ∃ u : ℂ, ‖u‖ = 1 ∧ u ^ 3 = (conj alpha) ^ 2 := by
  obtain ⟨u, hu⟩ := IsAlgClosed.exists_pow_nat_eq ((conj alpha) ^ 2) (by decide : 0 < 3)
  refine ⟨u, ?_, hu⟩
  have hn := congrArg norm hu
  simp only [norm_pow, Complex.norm_conj, alpha_unit, one_pow] at hn
  exact (pow_left_inj₀ (norm_nonneg u) (by norm_num : (0 : ℝ) ≤ 1)
    (by decide : (3 : ℕ) ≠ 0)).1 (by simpa using hn)

/-- A witness, without imposing a branch choice on the general theorem. -/
def u_p : ℂ := Classical.choose phase_exists
def u_pbar : ℂ := conj u_p

theorem u_p_unit : ‖u_p‖ = 1 := (Classical.choose_spec phase_exists).1
theorem u_p_cube : u_p ^ 3 = (conj alpha) ^ 2 :=
  (Classical.choose_spec phase_exists).2

theorem u_pbar_unit : ‖u_pbar‖ = 1 := by
  simpa [u_pbar] using u_p_unit

theorem u_pbar_cube : u_pbar ^ 3 = alpha ^ 2 := by
  simpa [u_pbar] using congrArg conj u_p_cube

/-- The real value of the conjugate-pair sum. -/
def combinedReal (u : ℂ) : ℝ := 2 * u.re

theorem combinedReal_cast (u : ℂ) : (combinedReal u : ℂ) = u + conj u := by
  apply Complex.ext <;> simp [combinedReal, two_mul]

theorem phase_polynomial (u : ℂ) (hunit : ‖u‖ = 1)
    (hcube : u ^ 3 = (conj alpha) ^ 2) :
    157 * combinedReal u ^ 3 - 471 * combinedReal u + 118 = 0 := by
  have hprod : u * conj u = 1 := by simpa [hunit] using Complex.mul_conj' u
  have hconj : (conj u) ^ 3 = alpha ^ 2 := by
    simpa using congrArg conj hcube
  have hc : (u + conj u) ^ 3 - 3 * (u + conj u) = -(118 / 157 : ℂ) := by
    calc
      _ = u ^ 3 + (conj u) ^ 3 + 3 * (u + conj u) * (u * conj u - 1) := by ring
      _ = -(118 / 157 : ℂ) := by rw [hprod, hcube, hconj, cube_target_sum]; ring
  rw [← combinedReal_cast] at hc
  have hr := congrArg Complex.re hc
  norm_num [← Complex.ofReal_pow] at hr
  nlinarith

theorem phase_upper_bound (u : ℂ) (hunit : ‖u‖ = 1) :
    |combinedReal u| ≤ 2 := by
  calc
    |combinedReal u| = 2 * |u.re| := by simp [combinedReal, abs_mul]
    _ ≤ 2 * ‖u‖ := mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm u) (by norm_num)
    _ = 2 := by rw [hunit]; norm_num

theorem phase_lower_bound (u : ℂ) (hunit : ‖u‖ = 1)
    (hcube : u ^ 3 = (conj alpha) ^ 2) :
    118 / 471 ≤ |combinedReal u| := by
  let x := combinedReal u
  change 118 / 471 ≤ |x|
  have hp : 157 * x ^ 3 - 471 * x + 118 = 0 := phase_polynomial u hunit hcube
  have hu : |x| ≤ 2 := phase_upper_bound u hunit
  have hx : x ^ 2 ≤ 4 := by
    simpa only [sq_abs, show (2 : ℝ) ^ 2 = 4 by norm_num] using
      (sq_le_sq₀ (abs_nonneg x) (by norm_num : (0 : ℝ) ≤ 2)).2 hu
  have hd : |x ^ 2 - 3| ≤ 3 := abs_le.2 ⟨by nlinarith [sq_nonneg x], by linarith⟩
  have he : x * (x ^ 2 - 3) = -(118 / 157 : ℝ) := by nlinarith [hp]
  have ha := congrArg abs he
  rw [abs_mul] at ha
  norm_num at ha
  have hm := mul_le_mul_of_nonneg_left hd (abs_nonneg x)
  nlinarith

theorem phase_nonzero (u : ℂ) (hunit : ‖u‖ = 1)
    (hcube : u ^ 3 = (conj alpha) ^ 2) : u + conj u ≠ 0 := by
  intro h
  have hr : combinedReal u = 0 := by
    simpa [combinedReal, two_mul] using congrArg Complex.re h
  have hl := phase_lower_bound u hunit hcube
  rw [hr, abs_zero] at hl
  norm_num at hl

/-- The chosen combined real phase. -/
def x : ℝ := combinedReal u_p

theorem x_is_pair : (x : ℂ) = u_p + u_pbar := combinedReal_cast u_p

theorem survival_polynomial : 157 * x ^ 3 - 471 * x + 118 = 0 :=
  phase_polynomial u_p u_p_unit u_p_cube

theorem survival_bounds : 118 / 471 ≤ |x| ∧ |x| ≤ 2 :=
  ⟨phase_lower_bound u_p u_p_unit u_p_cube, phase_upper_bound u_p u_p_unit⟩

theorem combined_phase_nonzero : u_p + u_pbar ≠ 0 :=
  phase_nonzero u_p u_p_unit u_p_cube

#print axioms omega_primitive
#print axioms omega_integral
#print axioms p_normSq
#print axioms pbar_normSq
#print axioms p_square
#print axioms phase_exists
#print axioms u_pbar_cube
#print axioms phase_polynomial
#print axioms phase_lower_bound
#print axioms survival_polynomial
#print axioms survival_bounds
#print axioms combined_phase_nonzero

end MetaplecticDictionary
