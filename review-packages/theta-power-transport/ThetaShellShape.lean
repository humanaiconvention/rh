import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Explicit theta-shell logarithmic-slope inequalities

Algebraic bounds from RH-PAIRED-SOURCE-001/CUMULATIVE-ORDER-AND-GATES.md,
equations (1)--(3), with the actual substitutions visible. This module
does not identify these expressions with derivatives of a shell density;
that bridge and the infinite-series passage are separate obligations.
No normalized full-density order or RH conclusion is asserted here.
-/

namespace ThetaMacdonald

noncomputable section

def shellZ (k : ℕ) (u : ℝ) : ℝ :=
  Real.pi * (k : ℝ) ^ 2 * Real.exp (2 * u)

def shellT (u : ℝ) : ℝ := Real.pi * Real.exp (2 * u)

def shellW (u : ℝ) : ℝ := Real.pi * Real.exp (-2 * u)

def logSlope (z t w : ℝ) : ℝ :=
  5 / 2 + 4 * z / (2 * z - 3) - 2 * z + 2 * t - 2 * w

def slopeDerivative (z t w : ℝ) : ℝ :=
  -(24 * z / (2 * z - 3) ^ 2) - 4 * z + 4 * t + 4 * w

theorem shellT_pos (u : ℝ) : 0 < shellT u :=
  mul_pos Real.pi_pos (Real.exp_pos _)

theorem shellW_pos (u : ℝ) : 0 < shellW u :=
  mul_pos Real.pi_pos (Real.exp_pos _)

theorem shellT_ge_pi {u : ℝ} (hu : 0 ≤ u) : Real.pi ≤ shellT u := by
  have he : (1 : ℝ) ≤ Real.exp (2 * u) :=
    Real.one_le_exp_iff.mpr (by linarith)
  have hm := mul_le_mul_of_nonneg_left he Real.pi_pos.le
  simpa only [mul_one, shellT] using hm

theorem shellT_le_shellZ_div_four {k : ℕ} (hk : 2 ≤ k) (u : ℝ) :
    shellT u ≤ shellZ k u / 4 := by
  have hkr : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hks : (4 : ℝ) ≤ (k : ℝ) ^ 2 := by
    nlinarith [sq_nonneg ((k : ℝ) - 2)]
  have hm := mul_le_mul_of_nonneg_left hks (shellT_pos u).le
  dsimp [shellT, shellZ] at *
  nlinarith

theorem shellW_le_shellT {u : ℝ} (hu : 0 ≤ u) : shellW u ≤ shellT u := by
  have he : Real.exp (-2 * u) ≤ Real.exp (2 * u) :=
    Real.exp_le_exp.mpr (by linarith)
  exact mul_le_mul_of_nonneg_left he Real.pi_pos.le

theorem shellW_le_shellZ_div_four {k : ℕ} (hk : 2 ≤ k) {u : ℝ}
    (hu : 0 ≤ u) : shellW u ≤ shellZ k u / 4 :=
  (shellW_le_shellT hu).trans (shellT_le_shellZ_div_four hk u)

theorem shellZ_gt_twelve {k : ℕ} (hk : 2 ≤ k) {u : ℝ} (hu : 0 ≤ u) :
    (12 : ℝ) < shellZ k u := by
  have ht := shellT_ge_pi hu
  have hz := shellT_le_shellZ_div_four hk u
  have hp := Real.pi_gt_three
  nlinarith

theorem shellT_mul_shellW (u : ℝ) : shellT u * shellW u = Real.pi ^ 2 := by
  dsimp [shellT, shellW]
  calc
    Real.pi * Real.exp (2 * u) * (Real.pi * Real.exp (-2 * u)) =
        Real.pi ^ 2 * (Real.exp (2 * u) * Real.exp (-2 * u)) := by ring
    _ = Real.pi ^ 2 := by
      rw [← Real.exp_add, show 2 * u + -2 * u = 0 by ring, Real.exp_zero, mul_one]

theorem shellW_eq_pi_sq_div_shellT (u : ℝ) :
    shellW u = Real.pi ^ 2 / shellT u := by
  apply (eq_div_iff (shellT_pos u).ne').2
  simpa only [mul_comm] using shellT_mul_shellW u

theorem shellZ_one (u : ℝ) : shellZ 1 u = shellT u := by
  simp [shellZ, shellT]

theorem logSlope_lt_of_ge_twelve {z t w : ℝ} (hz : 12 ≤ z)
    (ht : t ≤ z / 4) (hw : 0 ≤ w) :
    logSlope z t w < 5 - (3 / 2 : ℝ) * z := by
  have hd : 0 < 2 * z - 3 := by linarith
  have hf : 4 * z / (2 * z - 3) < (5 / 2 : ℝ) := by
    apply (div_lt_iff₀ hd).2
    linarith
  dsimp [logSlope]
  linarith

theorem slopeDerivative_gt_of_ge_twelve {z t w : ℝ} (hz : 12 ≤ z)
    (ht : 0 ≤ t) (hw : 0 ≤ w) :
    -5 * z < slopeDerivative z t w := by
  have hzp : 0 < z := by linarith
  have hd : 0 < 2 * z - 3 := by linarith
  have hds : 0 < (2 * z - 3) ^ 2 := sq_pos_of_pos hd
  have hsq : (24 : ℝ) < (2 * z - 3) ^ 2 := by
    nlinarith [sq_nonneg (z - 12)]
  have hf : (24 : ℝ) / (2 * z - 3) ^ 2 < 1 := by
    apply (div_lt_iff₀ hds).2
    simpa only [one_mul] using hsq
  have hm := mul_lt_mul_of_pos_right hf hzp
  have hterm : 24 * z / (2 * z - 3) ^ 2 < z := by
    calc
      _ = ((24 : ℝ) / (2 * z - 3) ^ 2) * z := by ring
      _ < 1 * z := hm
      _ = z := one_mul z
  dsimp [slopeDerivative]
  linarith

theorem curvature_factor_pos_of_ge_twelve {z t w : ℝ} (hz : 12 ≤ z)
    (ht0 : 0 ≤ t) (ht : t ≤ z / 4) (hw : 0 ≤ w) :
    0 < logSlope z t w ^ 2 + slopeDerivative z t w := by
  have hl := logSlope_lt_of_ge_twelve hz ht hw
  have hld := slopeDerivative_gt_of_ge_twelve hz ht0 hw
  have hb : 0 < (3 / 2 : ℝ) * z - 5 := by linarith
  have hsq : ((3 / 2 : ℝ) * z - 5) ^ 2 < logSlope z t w ^ 2 := by
    have ha : 0 < -logSlope z t w - ((3 / 2 : ℝ) * z - 5) := by linarith
    have hb' : 0 < -logSlope z t w + ((3 / 2 : ℝ) * z - 5) := by linarith
    nlinarith [mul_pos ha hb']
  have hpoly : 0 < ((3 / 2 : ℝ) * z - 5) ^ 2 - 5 * z := by
    nlinarith [sq_nonneg (z - 12)]
  linarith

theorem higher_shell_logSlope_lt {k : ℕ} (hk : 2 ≤ k) {u : ℝ} (hu : 0 ≤ u) :
    logSlope (shellZ k u) (shellT u) (shellW u) <
      5 - (3 / 2 : ℝ) * shellZ k u :=
  logSlope_lt_of_ge_twelve (shellZ_gt_twelve hk hu).le
    (shellT_le_shellZ_div_four hk u) (shellW_pos u).le

theorem higher_shell_logSlope_neg {k : ℕ} (hk : 2 ≤ k) {u : ℝ} (hu : 0 ≤ u) :
    logSlope (shellZ k u) (shellT u) (shellW u) < 0 := by
  have hl := higher_shell_logSlope_lt hk hu
  have hz := shellZ_gt_twelve hk hu
  linarith

theorem higher_shell_slopeDerivative_gt {k : ℕ} (hk : 2 ≤ k) {u : ℝ}
    (hu : 0 ≤ u) :
    -5 * shellZ k u < slopeDerivative (shellZ k u) (shellT u) (shellW u) :=
  slopeDerivative_gt_of_ge_twelve (shellZ_gt_twelve hk hu).le
    (shellT_pos u).le (shellW_pos u).le

theorem higher_shell_curvature_factor_pos {k : ℕ} (hk : 2 ≤ k) {u : ℝ}
    (hu : 0 ≤ u) :
    0 < logSlope (shellZ k u) (shellT u) (shellW u) ^ 2 +
      slopeDerivative (shellZ k u) (shellT u) (shellW u) :=
  curvature_factor_pos_of_ge_twelve (shellZ_gt_twelve hk hu).le
    (shellT_pos u).le (shellT_le_shellZ_div_four hk u) (shellW_pos u).le

/-- The first-shell derivative factor is positive for t at or above pi. -/
theorem first_slopeDerivative_pos_of_ge_pi {t : ℝ} (ht : Real.pi ≤ t) :
    0 < slopeDerivative t t (Real.pi ^ 2 / t) := by
  have hp := Real.pi_gt_three
  have ht0 : 0 < t := lt_of_lt_of_le Real.pi_pos ht
  have hd : 0 < 2 * t - 3 := by linarith
  have hds : 0 < (2 * t - 3) ^ 2 := sq_pos_of_pos hd
  have hp9 : (9 : ℝ) < Real.pi ^ 2 := by
    nlinarith [sq_nonneg (Real.pi - 3)]
  have hsq : t ^ 2 ≤ (2 * t - 3) ^ 2 := by
    nlinarith [sq_nonneg (t - 3)]
  have hprod : 9 * t ^ 2 < Real.pi ^ 2 * (2 * t - 3) ^ 2 := by
    calc
      _ < Real.pi ^ 2 * t ^ 2 := mul_lt_mul_of_pos_right hp9 (sq_pos_of_pos ht0)
      _ ≤ _ := mul_le_mul_of_nonneg_left hsq (sq_nonneg Real.pi)
  have hfrac : 24 * t / (2 * t - 3) ^ 2 < 4 * Real.pi ^ 2 / t := by
    apply (div_lt_div_iff₀ hds ht0).2
    nlinarith [sq_nonneg t]
  dsimp [slopeDerivative]
  convert sub_pos.mpr hfrac using 1 <;> ring

theorem first_shell_slopeDerivative_pos {u : ℝ} (hu : 0 ≤ u) :
    0 < slopeDerivative (shellZ 1 u) (shellT u) (shellW u) := by
  rw [shellZ_one, shellW_eq_pi_sq_div_shellT]
  exact first_slopeDerivative_pos_of_ge_pi (shellT_ge_pi hu)

theorem first_shell_curvature_factor_pos {u : ℝ} (hu : 0 ≤ u) :
    0 < logSlope (shellZ 1 u) (shellT u) (shellW u) ^ 2 +
      slopeDerivative (shellZ 1 u) (shellT u) (shellW u) := by
  have h := first_shell_slopeDerivative_pos hu
  nlinarith [sq_nonneg (logSlope (shellZ 1 u) (shellT u) (shellW u))]

theorem shell_curvature_factor_pos {k : ℕ} (hk : 1 ≤ k) {u : ℝ} (hu : 0 ≤ u) :
    0 < logSlope (shellZ k u) (shellT u) (shellW u) ^ 2 +
      slopeDerivative (shellZ k u) (shellT u) (shellW u) := by
  rcases eq_or_lt_of_le hk with h | h
  · subst k
    exact first_shell_curvature_factor_pos hu
  · exact higher_shell_curvature_factor_pos (Nat.succ_le_iff.mpr h) hu

end
end ThetaMacdonald

#print axioms ThetaMacdonald.higher_shell_logSlope_lt
#print axioms ThetaMacdonald.higher_shell_logSlope_neg
#print axioms ThetaMacdonald.higher_shell_slopeDerivative_gt
#print axioms ThetaMacdonald.higher_shell_curvature_factor_pos
#print axioms ThetaMacdonald.first_shell_slopeDerivative_pos
#print axioms ThetaMacdonald.first_shell_curvature_factor_pos
#print axioms ThetaMacdonald.shell_curvature_factor_pos
