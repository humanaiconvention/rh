import ThetaShellShape
import ThetaShellDerivative
import ThetaSeries

/-!
Exact actual-shell bridge. ratioRaw = phi_k / exp(-2 pi cosh(2u)).
The probability normalizers are not defined or assumed here.
-/
noncomputable section
namespace ThetaMacdonald

def referenceWeight (u : ℝ) : ℝ := Real.exp (shellT u + shellW u)
def ratioRaw (k : ℕ) (u : ℝ) : ℝ := rawShell k u * referenceWeight u
def ratioRawD1 (k : ℕ) (u : ℝ) : ℝ :=
  (rawShellD1 k u + rawShell k u * (2 * shellT u - 2 * shellW u)) *
    referenceWeight u
def ratioRawD2 (k : ℕ) (u : ℝ) : ℝ :=
  (rawShellD2 k u + 2 * rawShellD1 k u * (2 * shellT u - 2 * shellW u) +
    rawShell k u * ((2 * shellT u - 2 * shellW u)^2 + 4 * shellT u + 4 * shellW u)) *
    referenceWeight u

theorem hasDerivAt_shellT (u : ℝ) :
    HasDerivAt shellT (2 * shellT u) u := by
  convert hasDerivAt_zArg 1 u using 1
  · funext x
    simp [zArg, shellT]
  · simp [zArg, shellT]

theorem hasDerivAt_shellW (u : ℝ) :
    HasDerivAt shellW (-2 * shellW u) u := by
  have hu : HasDerivAt (fun x : ℝ => -2*x) (-2) u := by
    convert (hasDerivAt_id u).const_mul (-2) using 1 <;> simp
  convert hu.exp.const_mul Real.pi using 1
  · rfl
  · dsimp [shellW]
    ring

theorem hasDerivAt_referenceWeight (u : ℝ) :
    HasDerivAt referenceWeight
      ((2 * shellT u - 2 * shellW u) * referenceWeight u) u := by
  convert ((hasDerivAt_shellT u).add (hasDerivAt_shellW u)).exp using 1
  · rfl
  · dsimp [referenceWeight]
    ring

theorem hasDerivAt_ratioRaw (k : ℕ) (u : ℝ) :
    HasDerivAt (ratioRaw k) (ratioRawD1 k u) u := by
  convert (hasDerivAt_rawShell k u).mul (hasDerivAt_referenceWeight u) using 1
  · rfl
  · dsimp [ratioRawD1]
    ring

theorem hasDerivAt_ratioRawD1 (k : ℕ) (u : ℝ) :
    HasDerivAt (ratioRawD1 k) (ratioRawD2 k u) u := by
  have hf := ((hasDerivAt_shellT u).const_mul 2).sub
    ((hasDerivAt_shellW u).const_mul 2)
  have hp := (hasDerivAt_rawShellD1 k u).add
    ((hasDerivAt_rawShell k u).mul hf)
  convert hp.mul (hasDerivAt_referenceWeight u) using 1
  · rfl
  · dsimp [ratioRawD2]
    ring

theorem referenceWeight_eq_cosh (u : ℝ) :
    referenceWeight u = Real.exp (2 * Real.pi * Real.cosh (2*u)) := by
  unfold referenceWeight shellT shellW
  congr 1
  rw [Real.cosh_eq]
  congr 1 <;> ring

theorem rawShell_pos {k : ℕ} (hk : 1 ≤ k) {u : ℝ} (hu : 0 ≤ u) :
    0 < rawShell k u := by
  have hkr : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hks : (1 : ℝ) ≤ (k : ℝ)^2 := by nlinarith [sq_nonneg ((k : ℝ)-1)]
  have hm := mul_le_mul_of_nonneg_left hks (shellT_pos u).le
  have hzt : shellT u ≤ zArg k u := by
    dsimp [shellT, zArg] at *
    nlinarith
  have hz : (3 : ℝ) < zArg k u :=
    (Real.pi_gt_three.trans_le (shellT_ge_pi hu)).trans_le hzt
  unfold rawShell
  apply mul_pos _ (Real.exp_pos _)
  nlinarith

theorem ratioRaw_pos {k : ℕ} (hk : 1 ≤ k) {u : ℝ} (hu : 0 ≤ u) :
    0 < ratioRaw k u :=
  mul_pos (rawShell_pos hk hu) (Real.exp_pos _)

theorem ratioRawD2_eq_factor {k : ℕ} {u : ℝ}
    (hd : 2 * shellZ k u - 3 ≠ 0) :
    ratioRawD2 k u = ratioRaw k u *
      (logSlope (shellZ k u) (shellT u) (shellW u)^2 +
        slopeDerivative (shellZ k u) (shellT u) (shellW u)) := by
  have hz : zArg k u = shellZ k u := rfl
  let z := shellZ k u
  let t := shellT u
  let w := shellW u
  let d := 2*z-3
  let a := (5/2 : ℝ)-2*z+2*t-2*w
  let b := -4*z+4*t+4*w
  have hD : d ≠ 0 := hd
  have hL : logSlope z t w * d = a*d+4*z := by
    calc
      _ = (a+4*z/d)*d := by dsimp [logSlope, a, d]; ring
      _ = _ := by rw [add_mul, div_mul_cancel₀ _ hD]
  have hLp : slopeDerivative z t w * d^2 = -24*z+b*d^2 := by
    calc
      _ = (-(24*z/d^2)+b)*d^2 := by dsimp [slopeDerivative, b, d]; ring
      _ = _ := by
        rw [add_mul, neg_mul, div_mul_cancel₀ _ (pow_ne_zero 2 hD)]
        ring
  apply mul_right_cancel₀ (pow_ne_zero 2 hD)
  calc
    ratioRawD2 k u * d^2 =
        ratioRaw k u * ((logSlope z t w*d)^2+slopeDerivative z t w*d^2) := by
      rw [hL, hLp]
      dsimp [ratioRawD2, ratioRaw, rawShell, rawShellD1, rawShellD2, a, b, d, z, t, w]
      simp only [hz]
      ring
    _ = _ := by dsimp [z, t, w]; ring

theorem ratioRawD2_pos {k : ℕ} (hk : 1 ≤ k) {u : ℝ} (hu : 0 ≤ u) :
    0 < ratioRawD2 k u := by
  have hp := rawShell_pos hk hu
  have hz : (3 : ℝ) < shellZ k u := by
    rcases eq_or_lt_of_le hk with h | h
    · subst k
      rw [shellZ_one]
      exact Real.pi_gt_three.trans_le (shellT_ge_pi hu)
    · exact (by norm_num : (3 : ℝ) < 12).trans (shellZ_gt_twelve (Nat.succ_le_iff.mpr h) hu)
  rw [ratioRawD2_eq_factor (by linarith)]
  exact mul_pos (ratioRaw_pos hk hu) (shell_curvature_factor_pos hk hu)

theorem deriv_ratioRaw (k : ℕ) : deriv (ratioRaw k) = ratioRawD1 k :=
  funext fun u => (hasDerivAt_ratioRaw k u).deriv

theorem second_derivative_ratioRaw_pos {k : ℕ} (hk : 1 ≤ k) {u : ℝ}
    (hu : 0 ≤ u) :
    0 < deriv (deriv (ratioRaw k)) u := by
  rw [deriv_ratioRaw, (hasDerivAt_ratioRawD1 k u).deriv]
  exact ratioRawD2_pos hk hu

end ThetaMacdonald

#print axioms ThetaMacdonald.hasDerivAt_ratioRaw
#print axioms ThetaMacdonald.hasDerivAt_ratioRawD1
#print axioms ThetaMacdonald.referenceWeight_eq_cosh
#print axioms ThetaMacdonald.ratioRawD2_eq_factor
#print axioms ThetaMacdonald.second_derivative_ratioRaw_pos
