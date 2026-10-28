import CumulativeSplit
import ThetaDensityCrossing

/-! Strict cumulative order of the actual original normalized densities.
Every finite/tail sign premise is instantiated from the accepted crossing.
No cumulative sign, tail growth, moment order or zero location is assumed. -/
noncomputable section
open Set MeasureTheory
namespace ThetaMacdonald.Cumulative
open Density Mass

def densityDifference (t : ℝ) : ℝ := thetaDensity t-macdonaldDensity t
def cumulative (u : ℝ) : ℝ := ∫ t in (0 : ℝ)..u, densityDifference t

theorem integrable_densityDifference :
    IntegrableOn densityDifference (Ioi (0 : ℝ)) :=
  integrable_thetaDensity.sub integrable_macdonaldDensity

theorem integral_densityDifference_zero :
    (∫ t in Ioi (0 : ℝ), densityDifference t) = 0 := by
  unfold densityDifference
  rw [integral_sub integrable_thetaDensity integrable_macdonaldDensity,
    thetaDensity_mass, macdonaldDensity_mass, sub_self]

theorem cumulative_zero : cumulative 0 = 0 := by
  simp [cumulative]

theorem actual_finite_integrable {u : ℝ} (hu : 0 ≤ u) :
    IntervalIntegrable densityDifference volume 0 u :=
  SingleCrossing.intervalIntegrable_head integrable_densityDifference hu

theorem actual_tail_integrable {u : ℝ} (hu : 0 ≤ u) :
    IntegrableOn densityDifference (Ioi u) :=
  SingleCrossing.integrable_tail integrable_densityDifference hu

theorem cumulative_eq_Ioc {u : ℝ} (hu : 0 ≤ u) :
    cumulative u = ∫ t in Ioc (0 : ℝ) u, densityDifference t :=
  SingleCrossing.head_eq_Ioc hu

theorem cumulative_eq_Ioo {u : ℝ} (hu : 0 ≤ u) :
    cumulative u = ∫ t in Ioo (0 : ℝ) u, densityDifference t :=
  SingleCrossing.head_eq_Ioo hu

theorem cumulative_eq_Icc {u : ℝ} (hu : 0 ≤ u) :
    cumulative u = ∫ t in Icc (0 : ℝ) u, densityDifference t :=
  SingleCrossing.head_eq_Icc hu

theorem actual_head_tail_balance {u : ℝ} (hu : 0 ≤ u) :
    cumulative u + (∫ t in Ioi u, densityDifference t) = 0 := by
  have hs := SingleCrossing.head_tail_split integrable_densityDifference hu
  rw [integral_densityDifference_zero] at hs
  exact hs

theorem cumulative_eq_neg_tail {u : ℝ} (hu : 0 ≤ u) :
    cumulative u = -(∫ t in Ioi u, densityDifference t) := by
  have hs := actual_head_tail_balance hu
  linarith

theorem cumulative_eq_CDF_difference {u : ℝ} (hu : 0 ≤ u) :
    cumulative u =
      (∫ t in (0 : ℝ)..u, thetaDensity t) -
        (∫ t in (0 : ℝ)..u, macdonaldDensity t) := by
  unfold cumulative densityDifference
  rw [intervalIntegral.integral_sub
    (SingleCrossing.intervalIntegrable_head integrable_thetaDensity hu)
    (SingleCrossing.intervalIntegrable_head integrable_macdonaldDensity hu)]

/-- Strict cumulative order of the actual complete normalized sources. -/
theorem actual_cumulative_order {u : ℝ} (hu : 0 < u) :
    cumulative u < 0 := by
  obtain ⟨c, hc, he, hleft, hright, _⟩ := Crossing.actual_density_crossing
  exact SingleCrossing.strict_prefix_of_single_crossing
    integrable_densityDifference integral_densityDifference_zero
    (fun t ht htc => sub_neg.mpr (hleft t ht.le htc))
    (fun t hct => sub_pos.mpr (hright t hct)) hu

theorem actual_set_cumulative_order {u : ℝ} (hu : 0 < u) :
    (∫ t in Icc (0 : ℝ) u, densityDifference t) < 0 := by
  rw [← cumulative_eq_Icc hu.le]
  exact actual_cumulative_order hu

theorem actual_CDF_strict_order {u : ℝ} (hu : 0 < u) :
    (∫ t in (0 : ℝ)..u, thetaDensity t) <
      ∫ t in (0 : ℝ)..u, macdonaldDensity t := by
  have hs := actual_cumulative_order hu
  rw [cumulative_eq_CDF_difference hu.le] at hs
  exact sub_neg.mp hs

end ThetaMacdonald.Cumulative
#print axioms ThetaMacdonald.Cumulative.integral_densityDifference_zero
#print axioms ThetaMacdonald.Cumulative.cumulative_zero
#print axioms ThetaMacdonald.Cumulative.cumulative_eq_Icc
#print axioms ThetaMacdonald.Cumulative.actual_head_tail_balance
#print axioms ThetaMacdonald.Cumulative.cumulative_eq_neg_tail
#print axioms ThetaMacdonald.Cumulative.cumulative_eq_CDF_difference
#print axioms ThetaMacdonald.Cumulative.actual_cumulative_order
#print axioms ThetaMacdonald.Cumulative.actual_set_cumulative_order
#print axioms ThetaMacdonald.Cumulative.actual_CDF_strict_order
