import ThetaGaussianSeed
import ThetaPoissonReflection
import ThetaCompleteRatio

/-!
Actual theta symmetry and origin stationarity. The full integer Gaussian
and the nonnegative integer seed series are connected with both multiplicity
and the zero term retained. No evenness of the actual source is a premise.
-/
noncomputable section
open scoped BigOperators

namespace ThetaMacdonald.Symmetry

theorem gaussianSeed_zero (u : ℝ) :
    gaussianSeed 0 u = Real.exp (u/2) := by
  simp [gaussianSeed, zArg]

theorem centeredTheta_eq_full (u : ℝ) :
    centeredTheta u = Reflection.centeredFullTheta u := by
  let f : ℤ → ℝ := fun n =>
    Real.exp (u/2 - Real.pi * Real.exp (2*u) * (n : ℝ)^2)
  have hnat : HasSum (fun n : ℕ => f n) (gaussianSum u) := by
    change HasSum (fun n : ℕ => f n) (∑' k : ℕ, gaussianSeed k u)
    convert (summable_gaussianSeed u).hasSum using 1
    funext n
    dsimp [f, gaussianSeed, zArg]
    push_cast
    congr 1
    ring
  have hshift : Summable (fun n : ℕ => gaussianSeed (n+1) u) := by
    simpa only [Function.comp_def, Nat.succ_eq_add_one] using
      (summable_gaussianSeed u).comp_injective Nat.succ_injective
  have hneg : HasSum (fun n : ℕ => f (-(n+1))) (∑' n : ℕ, gaussianSeed (n+1) u) := by
    convert hshift.hasSum using 1
    funext n
    dsimp [f, gaussianSeed, zArg]
    push_cast
    congr 1
    ring
  have hint := hnat.of_nat_of_neg_add_one hneg
  have hfactor : f = fun n : ℤ =>
      Real.exp (u/2) * Real.exp (-Real.pi * Real.exp (2*u) * (n : ℝ)^2) := by
    funext n
    dsimp [f]
    rw [sub_eq_add_neg, Real.exp_add]
    congr 2 <;> ring
  have heq := hint.tsum_eq
  rw [hfactor, tsum_mul_left] at heq
  change Reflection.centeredFullTheta u =
    gaussianSum u + (∑' n : ℕ, gaussianSeed (n+1) u) at heq
  have hsplit : gaussianSum u =
      Real.exp (u/2) + (∑' n : ℕ, gaussianSeed (n+1) u) := by
    simpa only [gaussianSum, gaussianSeed_zero] using
      (summable_gaussianSeed u).tsum_eq_zero_add
  dsimp only [centeredTheta]
  linarith

theorem centeredTheta_even (u : ℝ) :
    centeredTheta (-u) = centeredTheta u := by
  rw [centeredTheta_eq_full, centeredTheta_eq_full]
  exact Reflection.centeredFullTheta_even u

theorem raw_sum_even (u : ℝ) :
    (∑' k : ℕ, rawShell k (-u)) = ∑' k : ℕ, rawShell k u := by
  rw [raw_sum_eq_centeredTheta, raw_sum_eq_centeredTheta,
    Reflection.second_deriv_even_of_even centeredTheta_even u,
    centeredTheta_even]

theorem referenceWeight_even (u : ℝ) :
    referenceWeight (-u) = referenceWeight u := by
  rw [referenceWeight_eq_cosh, referenceWeight_eq_cosh,
    show 2*(-u) = -(2*u) by ring, Real.cosh_neg]

theorem ratio_even (u : ℝ) :
    Complete.ratio (-u) = Complete.ratio u := by
  change (∑' k : ℕ, rawShell k (-u)) * referenceWeight (-u) =
    (∑' k : ℕ, rawShell k u) * referenceWeight u
  rw [raw_sum_even, referenceWeight_even]

/-- Exact cancellation of the complete raw derivative row at the origin. -/
theorem tsum_rawShellD1_zero :
    (∑' k : ℕ, rawShellD1 k 0) = 0 :=
  (Series.hasDerivAt_tsum_rawShell 0).deriv.symm.trans
    (Reflection.deriv_zero_of_even raw_sum_even)

/-- Stationarity of the actual complete ratio, not an assumed source symmetry. -/
theorem deriv_ratio_zero : deriv Complete.ratio 0 = 0 :=
  Reflection.deriv_zero_of_even ratio_even

theorem hasDerivAt_ratio_origin :
    HasDerivAt Complete.ratio 0 0 := by
  have hvalue : Complete.ratioD1 0 = 0 :=
    (Complete.hasDerivAt_ratio 0).deriv.symm.trans deriv_ratio_zero
  simpa only [hvalue] using Complete.hasDerivAt_ratio 0

end ThetaMacdonald.Symmetry

#print axioms ThetaMacdonald.Symmetry.centeredTheta_eq_full
#print axioms ThetaMacdonald.Symmetry.centeredTheta_even
#print axioms ThetaMacdonald.Symmetry.raw_sum_even
#print axioms ThetaMacdonald.Symmetry.referenceWeight_even
#print axioms ThetaMacdonald.Symmetry.ratio_even
#print axioms ThetaMacdonald.Symmetry.tsum_rawShellD1_zero
#print axioms ThetaMacdonald.Symmetry.deriv_ratio_zero
#print axioms ThetaMacdonald.Symmetry.hasDerivAt_ratio_origin
