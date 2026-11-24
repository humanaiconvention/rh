import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.MeasureTheory.Integral.Bochner.Set

noncomputable section
open Set MeasureTheory
namespace GaussDigamma

theorem difference_integral {a : ℝ} {z : ℂ} (ha : 0 < a) (hz : 0 < z.re) :
    Complex.digamma z - Complex.digamma (a : ℂ) =
      ∫ x in Ioi (0 : ℝ),
        ((Real.exp (-a * x) : ℂ) - Complex.exp (-z * (x : ℂ))) /
          (1 - (Real.exp (-x) : ℂ)) := by
  sorry

theorem integrable_difference {a : ℝ} {z : ℂ} (ha : 0 < a) (hz : 0 < z.re) :
    IntegrableOn (fun x : ℝ =>
      ((Real.exp (-a * x) : ℂ) - Complex.exp (-z * (x : ℂ))) /
        (1 - (Real.exp (-x) : ℂ))) (Ioi (0 : ℝ)) := by
  sorry
end GaussDigamma

set_option pp.all true in
#check @GaussDigamma.difference_integral
set_option pp.all true in
#check @GaussDigamma.integrable_difference
