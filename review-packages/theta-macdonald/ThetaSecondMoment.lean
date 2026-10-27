import ExponentialMomentBounds
import ThetaCumulativeOrder

/-! Actual second-moment order. The exponential bounds pay only for integrability
and tails; strictness retains the signed density difference at its unique crossing. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace ThetaMacdonald.SecondMoment
open Density Mass Cumulative

def thetaMajorant : ℝ := thetaTailConstant/gamma0
def macdonaldMajorant : ℝ := 2/macdonaldK0 (2*Real.pi)
def differenceMajorant : ℝ := thetaMajorant+macdonaldMajorant

theorem thetaMajorant_nonneg : 0 ≤ thetaMajorant := by
  apply div_nonneg _ gamma0_pos.le
  exact tsum_nonneg (fun k => by dsimp [thetaTailWeight]; positivity)

theorem macdonaldMajorant_pos : 0 < macdonaldMajorant :=
  div_pos (by norm_num) (macdonaldK0_pos (mul_pos (by norm_num) Real.pi_pos))

theorem differenceMajorant_pos : 0 < differenceMajorant :=
  add_pos_of_nonneg_of_pos thetaMajorant_nonneg macdonaldMajorant_pos

theorem thetaDensity_bound {u : ℝ} (hu : 0 ≤ u) :
    ‖thetaDensity u‖ ≤ thetaMajorant*Real.exp (-u) := by
  unfold thetaDensity thetaMajorant
  rw [norm_div, Real.norm_of_nonneg gamma0_pos.le]
  calc
    _ ≤ (thetaTailConstant*Real.exp (-u))/gamma0 :=
      div_le_div_of_nonneg_right (thetaProfile_tail_bound hu) gamma0_pos.le
    _ = _ := by ring

theorem macdonaldDensity_bound {u : ℝ} (hu : 0 ≤ u) :
    ‖macdonaldDensity u‖ ≤ macdonaldMajorant*Real.exp (-u) := by
  have hcosh0 := cosh_lower_half (show 0 ≤ 2*u by linarith)
  have hcosh : u ≤ Real.cosh (2*u) := by linarith
  have hpi : 1 ≤ 2*Real.pi := by linarith [Real.pi_gt_three]
  have hx : 0 ≤ 2*Real.pi := by positivity
  have hexp : macdonaldKernel (2*Real.pi) (2*u) ≤ Real.exp (-u) := by
    apply Real.exp_le_exp.mpr
    have h := mul_le_mul_of_nonneg_left hcosh hx
    have h2 := mul_le_mul_of_nonneg_right hpi hu
    linarith
  rw [Real.norm_of_nonneg (macdonaldDensity_pos u).le]
  unfold macdonaldDensity macdonaldMajorant
  calc
    _ ≤ (2*Real.exp (-u))/macdonaldK0 (2*Real.pi) :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hexp (by norm_num))
        (macdonaldK0_pos (mul_pos (by norm_num) Real.pi_pos)).le
    _ = _ := by ring

theorem densityDifference_bound {u : ℝ} (hu : 0 ≤ u) :
    ‖densityDifference u‖ ≤ differenceMajorant*Real.exp (-u) := by
  calc
    _ ≤ ‖thetaDensity u‖+‖macdonaldDensity u‖ := norm_sub_le _ _
    _ ≤ thetaMajorant*Real.exp (-u)+macdonaldMajorant*Real.exp (-u) :=
      add_le_add (thetaDensity_bound hu) (macdonaldDensity_bound hu)
    _ = _ := by unfold differenceMajorant; ring

theorem integrable_theta_secondMoment :
    IntegrableOn (fun u : ℝ => u^2*thetaDensity u) (Ioi (0 : ℝ)) :=
  ExponentialMoment.weighted_integrable integrable_thetaDensity
    (fun _ hu => thetaDensity_bound hu)

theorem integrable_macdonald_secondMoment :
    IntegrableOn (fun u : ℝ => u^2*macdonaldDensity u) (Ioi (0 : ℝ)) :=
  ExponentialMoment.weighted_integrable integrable_macdonaldDensity
    (fun _ hu => macdonaldDensity_bound hu)

theorem integrable_difference_secondMoment :
    IntegrableOn (fun u : ℝ => u^2*densityDifference u) (Ioi (0 : ℝ)) :=
  ExponentialMoment.weighted_integrable integrable_densityDifference
    (fun _ hu => densityDifference_bound hu)

theorem theta_secondMoment_tail {u : ℝ} (hu : 0 ≤ u) :
    ‖∫ t in Ioi u, t^2*thetaDensity t‖ ≤
      16*thetaMajorant*Real.exp (-u/2) :=
  ExponentialMoment.weighted_tail_bound thetaMajorant_nonneg
    (fun _ ht => thetaDensity_bound ht) hu

theorem macdonald_secondMoment_tail {u : ℝ} (hu : 0 ≤ u) :
    ‖∫ t in Ioi u, t^2*macdonaldDensity t‖ ≤
      16*macdonaldMajorant*Real.exp (-u/2) :=
  ExponentialMoment.weighted_tail_bound macdonaldMajorant_pos.le
    (fun _ ht => macdonaldDensity_bound ht) hu

theorem difference_secondMoment_tail {u : ℝ} (hu : 0 ≤ u) :
    ‖∫ t in Ioi u, t^2*densityDifference t‖ ≤
      16*differenceMajorant*Real.exp (-u/2) :=
  ExponentialMoment.weighted_tail_bound differenceMajorant_pos.le
    (fun _ ht => densityDifference_bound ht) hu

theorem cumulative_exponential_bound {u : ℝ} (hu : 0 ≤ u) :
    ‖cumulative u‖ ≤ differenceMajorant*Real.exp (-u) := by
  rw [cumulative_eq_neg_tail hu, norm_neg]
  exact ExponentialMoment.tail_bound (fun _ ht => densityDifference_bound ht) hu

theorem cumulative_secondMoment_boundary :
    Tendsto (fun u : ℝ => u^2*cumulative u) atTop (𝓝 0) :=
  ExponentialMoment.quadratic_boundary_vanishes
    (fun _ hu => cumulative_exponential_bound hu)

theorem centered_weight_integrable (c : ℝ) :
    IntegrableOn (fun u : ℝ => (u^2-c^2)*densityDifference u) (Ioi (0 : ℝ)) := by
  have hi := integrable_difference_secondMoment.sub
    (integrable_densityDifference.const_mul (c^2))
  apply hi.congr
  exact Eventually.of_forall (fun u => by dsimp; ring)

theorem actual_centered_secondMoment_pos :
    ∃ c : ℝ, 0 < c ∧
      0 < ∫ u in Ioi (0 : ℝ), (u^2-c^2)*densityDifference u := by
  obtain ⟨c, hc, he, hleft, hright, _⟩ := Crossing.actual_density_crossing
  refine ⟨c, hc, ?_⟩
  have hn : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))]
      (fun u : ℝ => (u^2-c^2)*densityDifference u) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    change 0 < u at hu
    rcases lt_trichotomy u c with huc | rfl | hcu
    · have hd : densityDifference u < 0 := sub_neg.mpr (hleft u hu.le huc)
      have hsq : u^2-c^2 < 0 := by nlinarith
      exact (mul_pos_of_neg_of_neg hsq hd).le
    · simp
    · have hd : 0 < densityDifference u := sub_pos.mpr (hright u hcu)
      have hsq : 0 < u^2-c^2 := by nlinarith
      exact (mul_pos hsq hd).le
  apply (setIntegral_pos_iff_support_of_nonneg_ae hn (centered_weight_integrable c)).2
  have hs : Ioi c ⊆
      Function.support (fun u : ℝ => (u^2-c^2)*densityDifference u) ∩ Ioi (0 : ℝ) := by
    intro u hu
    change c < u at hu
    have hd : 0 < densityDifference u := sub_pos.mpr (hright u hu)
    have hsq : 0 < u^2-c^2 := by nlinarith
    exact ⟨(mul_pos hsq hd).ne', hc.trans hu⟩
  exact lt_of_lt_of_le (by simp : 0 < volume (Ioi c)) (measure_mono hs)

theorem actual_difference_secondMoment_pos :
    0 < ∫ u in Ioi (0 : ℝ), u^2*densityDifference u := by
  obtain ⟨c, hc, hp⟩ := actual_centered_secondMoment_pos
  have he : (∫ u in Ioi (0 : ℝ), (u^2-c^2)*densityDifference u) =
      ∫ u in Ioi (0 : ℝ), u^2*densityDifference u := by
    calc
      _ = ∫ u in Ioi (0 : ℝ), u^2*densityDifference u-c^2*densityDifference u := by
        apply integral_congr_ae
        exact Eventually.of_forall (fun u => by ring)
      _ = _ := by
        rw [integral_sub integrable_difference_secondMoment
          (integrable_densityDifference.const_mul (c^2)), integral_const_mul,
          integral_densityDifference_zero, mul_zero, sub_zero]
  rwa [he] at hp

/-- Strict second-moment order of the actual original normalized densities. -/
theorem actual_secondMoment_order :
    (∫ u in Ioi (0 : ℝ), u^2*macdonaldDensity u) <
      ∫ u in Ioi (0 : ℝ), u^2*thetaDensity u := by
  have hp := actual_difference_secondMoment_pos
  have he : (∫ u in Ioi (0 : ℝ), u^2*densityDifference u) =
      (∫ u in Ioi (0 : ℝ), u^2*thetaDensity u) -
        ∫ u in Ioi (0 : ℝ), u^2*macdonaldDensity u := by
    calc
      _ = ∫ u in Ioi (0 : ℝ), u^2*thetaDensity u-u^2*macdonaldDensity u := by
        apply integral_congr_ae
        exact Eventually.of_forall (fun u => by unfold densityDifference; ring)
      _ = _ := integral_sub integrable_theta_secondMoment integrable_macdonald_secondMoment
  rw [he] at hp
  exact sub_pos.mp hp

end ThetaMacdonald.SecondMoment
#print axioms ThetaMacdonald.SecondMoment.thetaDensity_bound
#print axioms ThetaMacdonald.SecondMoment.macdonaldDensity_bound
#print axioms ThetaMacdonald.SecondMoment.densityDifference_bound
#print axioms ThetaMacdonald.SecondMoment.integrable_theta_secondMoment
#print axioms ThetaMacdonald.SecondMoment.integrable_macdonald_secondMoment
#print axioms ThetaMacdonald.SecondMoment.integrable_difference_secondMoment
#print axioms ThetaMacdonald.SecondMoment.theta_secondMoment_tail
#print axioms ThetaMacdonald.SecondMoment.macdonald_secondMoment_tail
#print axioms ThetaMacdonald.SecondMoment.difference_secondMoment_tail
#print axioms ThetaMacdonald.SecondMoment.cumulative_exponential_bound
#print axioms ThetaMacdonald.SecondMoment.cumulative_secondMoment_boundary
#print axioms ThetaMacdonald.SecondMoment.actual_centered_secondMoment_pos
#print axioms ThetaMacdonald.SecondMoment.actual_difference_secondMoment_pos
#print axioms ThetaMacdonald.SecondMoment.actual_secondMoment_order
