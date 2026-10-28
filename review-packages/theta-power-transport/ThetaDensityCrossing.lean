import ThetaDensityRatio
import Mathlib.Topology.Order.IntermediateValue

/-! Unique crossing of the original normalized densities on the positive
half-line. Equal mass, not a new tail-growth assumption, supplies both sides. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace ThetaMacdonald.Crossing
open Density Mass

theorem integral_Ioi_pos_of_everywhere_pos {f : ℝ → ℝ}
    (hi : IntegrableOn f (Ioi (0 : ℝ))) (hp : ∀ u : ℝ, 0 < u → 0 < f u) :
    0 < ∫ u in Ioi (0 : ℝ), f u := by
  have hn : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] f := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact (hp u hu).le
  apply (setIntegral_pos_iff_support_of_nonneg_ae hn hi).2
  have hs : Function.support f ∩ Ioi (0 : ℝ) = Ioi (0 : ℝ) := by
    ext u
    constructor
    · exact fun h => h.2
    · intro hu
      exact ⟨(hp u hu).ne', hu⟩
  rw [hs]
  simp

theorem ratio_origin_lt_one : likelihoodRatio 0 < 1 := by
  by_contra h
  have h0 : 1 ≤ likelihoodRatio 0 := le_of_not_gt h
  have hp : ∀ u : ℝ, 0 < u → 0 < thetaDensity u-macdonaldDensity u := by
    intro u hu
    have hr := strictMonoOn_likelihoodRatio (by simp : (0 : ℝ) ∈ Ici 0)
      hu.le hu
    exact sub_pos.mpr ((one_lt_ratio_iff u).mp (lt_of_le_of_lt h0 hr))
  have hi := integral_Ioi_pos_of_everywhere_pos
    (integrable_thetaDensity.sub integrable_macdonaldDensity) hp
  change 0 < ∫ u in Ioi (0 : ℝ), thetaDensity u-macdonaldDensity u at hi
  rw [integral_sub integrable_thetaDensity integrable_macdonaldDensity,
    thetaDensity_mass, macdonaldDensity_mass, sub_self] at hi
  exact (lt_irrefl (0 : ℝ)) hi

theorem exists_ratio_gt_one :
    ∃ u : ℝ, 0 < u ∧ 1 < likelihoodRatio u := by
  by_contra h
  have hle : ∀ u : ℝ, 0 < u → likelihoodRatio u ≤ 1 := by
    intro u hu
    exact le_of_not_gt (fun hr => h ⟨u, hu, hr⟩)
  have hp : ∀ u : ℝ, 0 < u → 0 < macdonaldDensity u-thetaDensity u := by
    intro u hu
    have hs := strictMonoOn_likelihoodRatio hu.le
      (show (0 : ℝ) ≤ u+1 by linarith) (show u < u+1 by linarith)
    have hr : likelihoodRatio u < 1 :=
      lt_of_lt_of_le hs (hle (u+1) (by linarith))
    exact sub_pos.mpr ((ratio_lt_one_iff u).mp hr)
  have hi := integral_Ioi_pos_of_everywhere_pos
    (integrable_macdonaldDensity.sub integrable_thetaDensity) hp
  change 0 < ∫ u in Ioi (0 : ℝ), macdonaldDensity u-thetaDensity u at hi
  rw [integral_sub integrable_macdonaldDensity integrable_thetaDensity,
    macdonaldDensity_mass, thetaDensity_mass, sub_self] at hi
  exact (lt_irrefl (0 : ℝ)) hi

theorem exists_positive_ratio_one :
    ∃ c : ℝ, 0 < c ∧ likelihoodRatio c = 1 := by
  obtain ⟨b, hb, hbr⟩ := exists_ratio_gt_one
  obtain ⟨c, hc, hr⟩ := intermediate_value_Icc hb.le
    continuous_likelihoodRatio.continuousOn ⟨ratio_origin_lt_one.le, hbr.le⟩
  refine ⟨c, ?_, hr⟩
  by_contra h
  have he : c = 0 := le_antisymm (le_of_not_gt h) hc.1
  rw [he] at hr
  exact ratio_origin_lt_one.ne hr

theorem unique_density_crossing :
    ∃! c : ℝ, 0 < c ∧ thetaDensity c = macdonaldDensity c := by
  obtain ⟨c, hc, hr⟩ := exists_positive_ratio_one
  refine ⟨c, ⟨hc, (ratio_eq_one_iff c).mp hr⟩, ?_⟩
  intro d hd
  apply strictMonoOn_likelihoodRatio.injOn hd.1.le hc.le
  rw [(ratio_eq_one_iff d).mpr hd.2, hr]

theorem density_crossing_sides {c : ℝ} (hc : 0 < c)
    (he : thetaDensity c = macdonaldDensity c) :
    (∀ u : ℝ, 0 ≤ u → u < c → thetaDensity u < macdonaldDensity u) ∧
    (∀ u : ℝ, c < u → macdonaldDensity u < thetaDensity u) := by
  have hr : likelihoodRatio c = 1 := (ratio_eq_one_iff c).mpr he
  constructor
  · intro u hu huc
    apply (ratio_lt_one_iff u).mp
    have h := strictMonoOn_likelihoodRatio hu hc.le huc
    rwa [hr] at h
  · intro u hcu
    apply (one_lt_ratio_iff u).mp
    have h := strictMonoOn_likelihoodRatio hc.le (le_of_lt (hc.trans hcu)) hcu
    rwa [hr] at h

theorem density_eq_iff_crossing {c : ℝ} (hc : 0 < c)
    (he : thetaDensity c = macdonaldDensity c) {u : ℝ} (hu : 0 ≤ u) :
    thetaDensity u = macdonaldDensity u ↔ u = c := by
  constructor
  · intro huEq
    apply strictMonoOn_likelihoodRatio.injOn hu hc.le
    rw [(ratio_eq_one_iff u).mpr huEq, (ratio_eq_one_iff c).mpr he]
  · intro h
    simpa only [h] using he

/-- Complete actual half-line crossing, including the endpoint and strict sides. -/
theorem actual_density_crossing :
    ∃ c : ℝ, 0 < c ∧ thetaDensity c = macdonaldDensity c ∧
      (∀ u : ℝ, 0 ≤ u → u < c → thetaDensity u < macdonaldDensity u) ∧
      (∀ u : ℝ, c < u → macdonaldDensity u < thetaDensity u) ∧
      (∀ u : ℝ, 0 ≤ u →
        (thetaDensity u = macdonaldDensity u ↔ u = c)) := by
  obtain ⟨c, hc, _⟩ := unique_density_crossing
  have hs := density_crossing_sides hc.1 hc.2
  exact ⟨c, hc.1, hc.2, hs.1, hs.2, fun _ hu => density_eq_iff_crossing hc.1 hc.2 hu⟩

end ThetaMacdonald.Crossing
#print axioms ThetaMacdonald.Crossing.ratio_origin_lt_one
#print axioms ThetaMacdonald.Crossing.exists_ratio_gt_one
#print axioms ThetaMacdonald.Crossing.exists_positive_ratio_one
#print axioms ThetaMacdonald.Crossing.unique_density_crossing
#print axioms ThetaMacdonald.Crossing.density_crossing_sides
#print axioms ThetaMacdonald.Crossing.actual_density_crossing
