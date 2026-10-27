import ThetaOrderCore

/-!
# Curvature of the complete, unnormalized theta/reference ratio

The actual compact-local convergence and both differentiated raw-shell series
are imported from the accepted source. Product rules differentiate the complete
sum. At a fixed argument, HasSum transports all three convergent derivative rows
through the exact finite linear combination. Positivity uses the actual first
nonzero shell and nonnegativity of every other shell, including index zero.

No probability normalizer, origin stationarity, cumulative order or zero
location is assumed or concluded.
-/

noncomputable section
open scoped BigOperators

namespace ThetaMacdonald.Complete

def ratio (u : ℝ) : ℝ :=
  (∑' k : ℕ, rawShell k u) * referenceWeight u

def ratioD1 (u : ℝ) : ℝ :=
  ((∑' k : ℕ, rawShellD1 k u) +
    (∑' k : ℕ, rawShell k u) * (2 * shellT u - 2 * shellW u)) *
      referenceWeight u

def ratioD2 (u : ℝ) : ℝ :=
  ((∑' k : ℕ, rawShellD2 k u) +
    2 * (∑' k : ℕ, rawShellD1 k u) * (2 * shellT u - 2 * shellW u) +
    (∑' k : ℕ, rawShell k u) *
      ((2 * shellT u - 2 * shellW u)^2 + 4 * shellT u + 4 * shellW u)) *
        referenceWeight u

/-- Exact source indexing and the actual positive reference denominator. -/
theorem ratio_eq_source_quotient (u : ℝ) :
    ratio u = (∑' n : ℕ, rawShell (n + 1) u) /
      Real.exp (-(2 * Real.pi * Real.cosh (2 * u))) := by
  rw [ratio, Series.tsum_rawShell_eq_shifted, referenceWeight_eq_cosh,
    Real.exp_neg, div_inv_eq_mul]

/-- The complete ratio really is the convergent sum of the shell ratios. -/
theorem hasSum_ratioRaw (u : ℝ) :
    HasSum (fun k : ℕ => ratioRaw k u) (ratio u) := by
  simpa only [ratioRaw, ratio] using
    (Series.summable_rawShell u).hasSum.mul_right (referenceWeight u)

theorem hasDerivAt_ratio (u : ℝ) :
    HasDerivAt ratio (ratioD1 u) u := by
  convert (Series.hasDerivAt_tsum_rawShell u).mul
    (hasDerivAt_referenceWeight u) using 1
  · rfl
  · dsimp [ratioD1]
    ring

theorem hasDerivAt_ratioD1 (u : ℝ) :
    HasDerivAt ratioD1 (ratioD2 u) u := by
  have hphase := ((hasDerivAt_shellT u).const_mul 2).sub
    ((hasDerivAt_shellW u).const_mul 2)
  have hhead := (Series.hasDerivAt_tsum_rawShellD1 u).add
    ((Series.hasDerivAt_tsum_rawShell u).mul hphase)
  convert hhead.mul (hasDerivAt_referenceWeight u) using 1
  · rfl
  · dsimp [ratioD2]
    ring

/-- Every scalar and companion is retained before taking the infinite sum. -/
theorem hasSum_ratioRawD2 (u : ℝ) :
    HasSum (fun k : ℕ => ratioRawD2 k u) (ratioD2 u) := by
  have h0 := (Series.summable_rawShell u).hasSum
  have h1 := (Series.summable_rawShellD1 u).hasSum
  have h2 := (Series.summable_rawShellD2 u).hasSum
  exact ((h2.add ((h1.mul_left 2).mul_right
      (2 * shellT u - 2 * shellW u))).add
    (h0.mul_right
      ((2 * shellT u - 2 * shellW u)^2 + 4 * shellT u + 4 * shellW u))).mul_right
        (referenceWeight u)

theorem summable_ratioRawD2 (u : ℝ) :
    Summable (fun k : ℕ => ratioRawD2 k u) :=
  (hasSum_ratioRawD2 u).summable

theorem second_deriv_ratio_eq_tsum (u : ℝ) :
    deriv (deriv ratio) u = ∑' k : ℕ, ratioRawD2 k u := by
  have hd : deriv ratio = ratioD1 :=
    funext fun v => (hasDerivAt_ratio v).deriv
  rw [hd, (hasDerivAt_ratioD1 u).deriv, (hasSum_ratioRawD2 u).tsum_eq]

theorem ratioRawD2_zero (u : ℝ) : ratioRawD2 0 u = 0 := by
  simp [ratioRawD2, rawShell, rawShellD1, rawShellD2, zArg]

/-- Strict curvature of the actual complete infinite ratio on the half-line. -/
theorem second_deriv_ratio_pos {u : ℝ} (hu : 0 ≤ u) :
    0 < deriv (deriv ratio) u := by
  rw [second_deriv_ratio_eq_tsum]
  have hnonneg : ∀ k : ℕ, 0 ≤ ratioRawD2 k u := by
    intro k
    by_cases hk : k = 0
    · subst k
      rw [ratioRawD2_zero]
    · exact (ratioRawD2_pos (by omega) hu).le
  have hone : 0 < ratioRawD2 1 u := ratioRawD2_pos (by norm_num) hu
  exact (summable_ratioRawD2 u).tsum_pos hnonneg 1 hone

end ThetaMacdonald.Complete

#print axioms ThetaMacdonald.Complete.ratio_eq_source_quotient
#print axioms ThetaMacdonald.Complete.hasSum_ratioRaw
#print axioms ThetaMacdonald.Complete.hasDerivAt_ratio
#print axioms ThetaMacdonald.Complete.hasDerivAt_ratioD1
#print axioms ThetaMacdonald.Complete.hasSum_ratioRawD2
#print axioms ThetaMacdonald.Complete.summable_ratioRawD2
#print axioms ThetaMacdonald.Complete.second_deriv_ratio_eq_tsum
#print axioms ThetaMacdonald.Complete.ratioRawD2_zero
#print axioms ThetaMacdonald.Complete.second_deriv_ratio_pos
