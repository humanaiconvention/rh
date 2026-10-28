import CoordinateSingleCrossing
import ThetaMomentOrder

/-! One uniform natural-power coordinate family on the actual normalized sources.
Sharpness concerns Lipschitz functions of u^k, not physical Lipschitzness in u. -/
noncomputable section
open Set MeasureTheory Filter
open scoped NNReal
namespace ThetaMacdonald.PowerCoordinate
open Density Mass Cumulative Moment

def powerMomentGap (k : ℕ) : ℝ :=
  (∫ u in Ioi (0 : ℝ), u^k * thetaDensity u) -
    ∫ u in Ioi (0 : ℝ), u^k * macdonaldDensity u

theorem powerMomentGap_pos (k : ℕ) (hk : 0 < k) : 0 < powerMomentGap k :=
  sub_pos.mpr (actual_power_moment_order k hk)

theorem powerMomentGap_eq_signed (k : ℕ) :
    powerMomentGap k = ∫ u in Ioi (0 : ℝ), u^k * densityDifference u := by
  rw [powerMomentGap, ← integral_sub (integrable_theta_power k) (integrable_macdonald_power k)]
  apply integral_congr_ae
  exact Eventually.of_forall (fun u => by dsimp [densityDifference]; ring)

theorem actual_power_coordinate_measurable (k : ℕ) :
    AEMeasurable (fun u : ℝ => u^k) (volume.restrict (Ioi (0 : ℝ))) :=
  (measurable_id.pow_const k).aemeasurable

theorem actual_power_crossing_ae (k : ℕ) :
    ∃ a : ℝ, ∀ᵐ u ∂(volume.restrict (Ioi (0 : ℝ))),
      0 ≤ (u^k - a) * densityDifference u := by
  obtain ⟨c, hc, he, hl, hr, _⟩ := Crossing.actual_density_crossing
  refine ⟨c^k, ?_⟩
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  rcases lt_trichotomy u c with huc | rfl | hcu
  · exact mul_nonneg_of_nonpos_of_nonpos
      (sub_nonpos.mpr (pow_le_pow_left₀ hu.le huc.le k))
      (sub_neg.mpr (hl u hu.le huc)).le
  · simp
  · exact mul_nonneg (sub_nonneg.mpr (pow_le_pow_left₀ hc.le hcu.le k))
      (sub_pos.mpr (hr u hcu)).le

theorem actual_power_weighted_integrable (k : ℕ) {φ : ℝ → ℝ} {K : ℝ≥0}
    (hφ : LipschitzWith K φ) :
    IntegrableOn (fun u => φ (u^k) * thetaDensity u) (Ioi (0 : ℝ)) ∧
      IntegrableOn (fun u => φ (u^k) * macdonaldDensity u) (Ioi (0 : ℝ)) :=
  ⟨CoordinateSingleCrossing.lipschitz_comp_mul_integrable (actual_power_coordinate_measurable k)
      integrable_thetaDensity (integrable_theta_power k) hφ,
   CoordinateSingleCrossing.lipschitz_comp_mul_integrable (actual_power_coordinate_measurable k)
      integrable_macdonaldDensity (integrable_macdonald_power k) hφ⟩

theorem actual_power_lipschitz_gap_le (k : ℕ) {φ : ℝ → ℝ} {K : ℝ≥0}
    (hφ : LipschitzWith K φ) :
    |(∫ u in Ioi (0 : ℝ), φ (u^k) * thetaDensity u) -
      ∫ u in Ioi (0 : ℝ), φ (u^k) * macdonaldDensity u| ≤
        (K : ℝ) * powerMomentGap k := by
  obtain ⟨a, hs⟩ := actual_power_crossing_ae k
  have h := CoordinateSingleCrossing.abs_integral_comp_le_coordinate_moment
    (actual_power_coordinate_measurable k) integrable_densityDifference
    (integrable_difference_power k) integral_densityDifference_zero hs hφ
  have hi := actual_power_weighted_integrable k hφ
  rw [powerMomentGap_eq_signed]
  have he : (∫ u in Ioi (0 : ℝ), φ (u^k) * thetaDensity u) -
      (∫ u in Ioi (0 : ℝ), φ (u^k) * macdonaldDensity u) =
        ∫ u in Ioi (0 : ℝ), φ (u^k) * densityDifference u := by
    rw [← integral_sub hi.1 hi.2]
    apply integral_congr_ae
    exact Eventually.of_forall (fun u => by dsimp [densityDifference]; ring)
  rwa [he]

theorem actual_positive_power_budget_iff (k : ℕ) (hk : 0 < k) {B : ℝ} :
    (∀ φ : ℝ → ℝ, LipschitzWith 1 φ →
      |(∫ u in Ioi (0 : ℝ), φ (u^k) * thetaDensity u) -
        ∫ u in Ioi (0 : ℝ), φ (u^k) * macdonaldDensity u| ≤ B) ↔
      powerMomentGap k ≤ B := by
  constructor
  · intro h
    have hid := h id LipschitzWith.id
    change |powerMomentGap k| ≤ B at hid
    rwa [abs_of_pos (powerMomentGap_pos k hk)] at hid
  · intro hB φ hφ
    have h := actual_power_lipschitz_gap_le k hφ
    calc
      _ ≤ powerMomentGap k := by simpa only [NNReal.coe_one, one_mul] using h
      _ ≤ B := hB

end ThetaMacdonald.PowerCoordinate
#print axioms ThetaMacdonald.PowerCoordinate.powerMomentGap_pos
#print axioms ThetaMacdonald.PowerCoordinate.powerMomentGap_eq_signed
#print axioms ThetaMacdonald.PowerCoordinate.actual_power_coordinate_measurable
#print axioms ThetaMacdonald.PowerCoordinate.actual_power_crossing_ae
#print axioms ThetaMacdonald.PowerCoordinate.actual_power_weighted_integrable
#print axioms ThetaMacdonald.PowerCoordinate.actual_power_lipschitz_gap_le
#print axioms ThetaMacdonald.PowerCoordinate.actual_positive_power_budget_iff
