import MonotoneMomentOrder
import ThetaSecondMoment

/-! The generic weighted comparison is fully instantiated on the original
theta and Macdonald densities. Each fixed natural exponent is integrable. -/
noncomputable section
open Set Filter MeasureTheory
namespace ThetaMacdonald.Moment
open Density Mass Cumulative SecondMoment

theorem integrable_theta_power (n : ℕ) :
    IntegrableOn (fun u : ℝ => u^n*thetaDensity u) (Ioi (0 : ℝ)) :=
  ExponentialMoment.power_weighted_integrable n integrable_thetaDensity
    (fun _ hu => thetaDensity_bound hu)

theorem integrable_macdonald_power (n : ℕ) :
    IntegrableOn (fun u : ℝ => u^n*macdonaldDensity u) (Ioi (0 : ℝ)) :=
  ExponentialMoment.power_weighted_integrable n integrable_macdonaldDensity
    (fun _ hu => macdonaldDensity_bound hu)

theorem integrable_difference_power (n : ℕ) :
    IntegrableOn (fun u : ℝ => u^n*densityDifference u) (Ioi (0 : ℝ)) :=
  ExponentialMoment.power_weighted_integrable n integrable_densityDifference
    (fun _ hu => densityDifference_bound hu)

/-- Any integrable monotone weight increasing somewhere above the actual
crossing strictly orders the two actual densities. -/
theorem actual_monotone_weight_order {w : ℝ → ℝ}
    (hwm : IntegrableOn (fun u => w u*thetaDensity u) (Ioi (0 : ℝ)))
    (hwn : IntegrableOn (fun u => w u*macdonaldDensity u) (Ioi (0 : ℝ)))
    (hw : MonotoneOn w (Ioi (0 : ℝ)))
    (hstrict : ∀ c : ℝ, 0 < c → ∃ b : ℝ, c < b ∧ w c < w b) :
    (∫ u in Ioi (0 : ℝ), w u*macdonaldDensity u) <
      ∫ u in Ioi (0 : ℝ), w u*thetaDensity u := by
  obtain ⟨c, hc, he, hleft, hright, _⟩ := Crossing.actual_density_crossing
  apply SingleCrossing.strict_integral_order_of_monotone_weight
    integrable_thetaDensity integrable_macdonaldDensity hwm hwn
    (by rw [thetaDensity_mass, macdonaldDensity_mass]) hc
    (fun u hu huc => hleft u hu.le huc) hright hw (hstrict c hc)

/-- Strict order for every fixed positive natural power, not just even ones. -/
theorem actual_power_moment_order (n : ℕ) (hn : 0 < n) :
    (∫ u in Ioi (0 : ℝ), u^n*macdonaldDensity u) <
      ∫ u in Ioi (0 : ℝ), u^n*thetaDensity u := by
  apply actual_monotone_weight_order (integrable_theta_power n) (integrable_macdonald_power n)
  · intro x hx y hy hxy
    exact pow_le_pow_left₀ hx.le hxy n
  · intro c hc
    refine ⟨c+1, by linarith, ?_⟩
    exact pow_lt_pow_left₀ (by linarith) hc.le (Nat.ne_of_gt hn)

theorem actual_positive_even_moment_order (j : ℕ) (hj : 0 < j) :
    (∫ u in Ioi (0 : ℝ), u^(2*j)*macdonaldDensity u) <
      ∫ u in Ioi (0 : ℝ), u^(2*j)*thetaDensity u :=
  actual_power_moment_order (2*j) (Nat.mul_pos (by norm_num) hj)

theorem actual_zeroth_moment_equal :
    (∫ u in Ioi (0 : ℝ), u^0*macdonaldDensity u) =
      ∫ u in Ioi (0 : ℝ), u^0*thetaDensity u := by
  simp only [pow_zero, one_mul, macdonaldDensity_mass, thetaDensity_mass]

end ThetaMacdonald.Moment
#print axioms ThetaMacdonald.Moment.integrable_theta_power
#print axioms ThetaMacdonald.Moment.integrable_macdonald_power
#print axioms ThetaMacdonald.Moment.integrable_difference_power
#print axioms ThetaMacdonald.Moment.actual_monotone_weight_order
#print axioms ThetaMacdonald.Moment.actual_power_moment_order
#print axioms ThetaMacdonald.Moment.actual_positive_even_moment_order
#print axioms ThetaMacdonald.Moment.actual_zeroth_moment_equal
