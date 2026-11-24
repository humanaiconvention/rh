import GaussDigamma

noncomputable section
open Set MeasureTheory

namespace GaussDigammaConsumer

theorem difference {a : ℝ} {z : ℂ} (ha : 0 < a) (hz : 0 < z.re) :
    Complex.digamma z - Complex.digamma (a : ℂ) =
      ∫ x in Ioi (0 : ℝ),
        ((Real.exp (-a * x) : ℂ) - Complex.exp (-z * (x : ℂ))) /
          (1 - (Real.exp (-x) : ℂ)) :=
  GaussDigamma.difference_integral ha hz

theorem integrability {a : ℝ} {z : ℂ} (ha : 0 < a) (hz : 0 < z.re) :
    IntegrableOn (fun x : ℝ =>
      ((Real.exp (-a * x) : ℂ) - Complex.exp (-z * (x : ℂ))) /
        (1 - (Real.exp (-x) : ℂ))) (Ioi (0 : ℝ)) :=
  GaussDigamma.integrable_difference ha hz

end GaussDigammaConsumer

#print axioms GaussDigammaConsumer.difference
#print axioms GaussDigammaConsumer.integrability
