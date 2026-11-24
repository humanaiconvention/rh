import DigammaGauss

/-!
# Gauss digamma difference: public package interface

The reference parameter is positive real; the second parameter is complex
with positive real part. Integrability is proved rather than assumed.
The unchanged provider is DigammaGauss.lean. No wider domain is asserted.
-/

noncomputable section
open Set MeasureTheory

namespace GaussDigamma

theorem difference_integral {a : ℝ} {z : ℂ} (ha : 0 < a) (hz : 0 < z.re) :
    Complex.digamma z - Complex.digamma (a : ℂ) =
      ∫ x in Ioi (0 : ℝ),
        ((Real.exp (-a * x) : ℂ) - Complex.exp (-z * (x : ℂ))) /
          (1 - (Real.exp (-x) : ℂ)) :=
  DigammaGauss.digamma_difference_exp ha hz

theorem integrable_difference {a : ℝ} {z : ℂ} (ha : 0 < a) (hz : 0 < z.re) :
    IntegrableOn (fun x : ℝ =>
      ((Real.exp (-a * x) : ℂ) - Complex.exp (-z * (x : ℂ))) /
        (1 - (Real.exp (-x) : ℂ))) (Ioi (0 : ℝ)) :=
  DigammaGauss.gauss_integrable_exp ha hz

end GaussDigamma

#print axioms GaussDigamma.difference_integral
#print axioms GaussDigamma.integrable_difference
