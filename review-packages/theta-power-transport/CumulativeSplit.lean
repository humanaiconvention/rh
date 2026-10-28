import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic

/-! Finite/tail bookkeeping and strict prefix sign from a single crossing.
All integrability and pointwise-sign premises are explicit; no cumulative
sign is assumed. This helper is instantiated on the actual densities. -/
noncomputable section
open Set Filter MeasureTheory
namespace SingleCrossing

theorem integrable_tail {f : ℝ → ℝ}
    (hf : IntegrableOn f (Ioi (0 : ℝ))) {u : ℝ} (hu : 0 ≤ u) :
    IntegrableOn f (Ioi u) :=
  hf.mono_set (Ioi_subset_Ioi hu)

theorem intervalIntegrable_head {f : ℝ → ℝ}
    (hf : IntegrableOn f (Ioi (0 : ℝ))) {u : ℝ} (hu : 0 ≤ u) :
    IntervalIntegrable f volume 0 u :=
  (intervalIntegrable_iff_integrableOn_Ioc_of_le hu).2
    (hf.mono_set Ioc_subset_Ioi_self)

theorem head_tail_split {f : ℝ → ℝ}
    (hf : IntegrableOn f (Ioi (0 : ℝ))) {u : ℝ} (hu : 0 ≤ u) :
    (∫ t in (0 : ℝ)..u, f t)+(∫ t in Ioi u, f t) =
      ∫ t in Ioi (0 : ℝ), f t :=
  intervalIntegral.integral_interval_add_Ioi hf (integrable_tail hf hu)

theorem head_eq_Ioc {f : ℝ → ℝ} {u : ℝ} (hu : 0 ≤ u) :
    (∫ t in (0 : ℝ)..u, f t) = ∫ t in Ioc (0 : ℝ) u, f t :=
  intervalIntegral.integral_of_le hu

theorem head_eq_Ioo {f : ℝ → ℝ} {u : ℝ} (hu : 0 ≤ u) :
    (∫ t in (0 : ℝ)..u, f t) = ∫ t in Ioo (0 : ℝ) u, f t := by
  rw [head_eq_Ioc hu, integral_Ioc_eq_integral_Ioo]

theorem head_eq_Icc {f : ℝ → ℝ} {u : ℝ} (hu : 0 ≤ u) :
    (∫ t in (0 : ℝ)..u, f t) = ∫ t in Icc (0 : ℝ) u, f t := by
  rw [head_eq_Ioc hu, integral_Icc_eq_integral_Ioc]

theorem integral_tail_pos {f : ℝ → ℝ} {u : ℝ}
    (hf : IntegrableOn f (Ioi u)) (hp : ∀ t : ℝ, u < t → 0 < f t) :
    0 < ∫ t in Ioi u, f t := by
  have hn : 0 ≤ᵐ[volume.restrict (Ioi u)] f := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact (hp t ht).le
  apply (setIntegral_pos_iff_support_of_nonneg_ae hn hf).2
  have hs : Function.support f ∩ Ioi u = Ioi u := by
    ext t
    constructor
    · exact fun h => h.2
    · intro ht
      exact ⟨(hp t ht).ne', ht⟩
  rw [hs]
  simp

theorem strict_prefix_of_single_crossing {f : ℝ → ℝ} {c : ℝ}
    (hf : IntegrableOn f (Ioi (0 : ℝ)))
    (hzero : (∫ t in Ioi (0 : ℝ), f t) = 0)
    (hneg : ∀ t : ℝ, 0 < t → t < c → f t < 0)
    (hpos : ∀ t : ℝ, c < t → 0 < f t)
    {u : ℝ} (hu : 0 < u) :
    (∫ t in (0 : ℝ)..u, f t) < 0 := by
  by_cases huc : u ≤ c
  · have hi := intervalIntegrable_head hf hu.le
    have hp := intervalIntegral.intervalIntegral_pos_of_pos_on hi.neg
      (fun t ht => neg_pos.mpr (hneg t ht.1 (lt_of_lt_of_le ht.2 huc))) hu
    change 0 < ∫ t in (0 : ℝ)..u, -f t at hp
    rw [intervalIntegral.integral_neg] at hp
    linarith
  · have hcu : c < u := lt_of_not_ge huc
    have hp := integral_tail_pos (integrable_tail hf hu.le)
      (fun t ht => hpos t (hcu.trans ht))
    have hs := head_tail_split hf hu.le
    rw [hzero] at hs
    linarith

end SingleCrossing
#print axioms SingleCrossing.head_tail_split
#print axioms SingleCrossing.head_eq_Ioc
#print axioms SingleCrossing.head_eq_Ioo
#print axioms SingleCrossing.head_eq_Icc
#print axioms SingleCrossing.strict_prefix_of_single_crossing
