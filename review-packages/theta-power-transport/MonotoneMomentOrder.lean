import ExponentialMomentBounds

/-! A single signed crossing and equal mass imply strict monotone-weight
order when the weight increases somewhere above the crossing. -/
noncomputable section
open Set Filter MeasureTheory
namespace SingleCrossing

theorem strict_integral_order_of_monotone_weight
    {f g w : ℝ → ℝ} {c : ℝ}
    (hf : IntegrableOn f (Ioi (0 : ℝ)))
    (hg : IntegrableOn g (Ioi (0 : ℝ)))
    (hwf : IntegrableOn (fun u => w u*f u) (Ioi (0 : ℝ)))
    (hwg : IntegrableOn (fun u => w u*g u) (Ioi (0 : ℝ)))
    (hmass : (∫ u in Ioi (0 : ℝ), f u) = ∫ u in Ioi (0 : ℝ), g u)
    (hc : 0 < c)
    (hleft : ∀ u : ℝ, 0 < u → u < c → f u < g u)
    (hright : ∀ u : ℝ, c < u → g u < f u)
    (hw : MonotoneOn w (Ioi (0 : ℝ)))
    (hstrict : ∃ b : ℝ, c < b ∧ w c < w b) :
    (∫ u in Ioi (0 : ℝ), w u*g u) <
      ∫ u in Ioi (0 : ℝ), w u*f u := by
  let d : ℝ → ℝ := fun u => f u-g u
  let h : ℝ → ℝ := fun u => (w u-w c)*d u
  have hd : IntegrableOn d (Ioi (0 : ℝ)) := hf.sub hg
  have hwd : IntegrableOn (fun u => w u*d u) (Ioi (0 : ℝ)) := by
    apply (hwf.sub hwg).congr
    exact Eventually.of_forall (fun u => by dsimp [d]; ring)
  have hi : IntegrableOn h (Ioi (0 : ℝ)) := by
    apply (hwd.sub (hd.const_mul (w c))).congr
    exact Eventually.of_forall (fun u => by dsimp [h]; ring)
  have hn : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] h := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    change 0 < u at hu
    dsimp [h,d]
    rcases lt_trichotomy u c with huc | rfl | hcu
    · exact mul_nonneg_of_nonpos_of_nonpos
        (sub_nonpos.mpr (hw hu hc huc.le)) (sub_neg.mpr (hleft u hu huc)).le
    · simp
    · exact mul_nonneg (sub_nonneg.mpr (hw hc hu hcu.le))
        (sub_pos.mpr (hright u hcu)).le
  obtain ⟨b, hcb, hwb⟩ := hstrict
  have hs : Ioi b ⊆ Function.support h ∩ Ioi (0 : ℝ) := by
    intro u hu
    change b < u at hu
    have hcu : c < u := hcb.trans hu
    have hwu : 0 < w u-w c :=
      sub_pos.mpr (hwb.trans_le (hw (hc.trans hcb) (hc.trans hcu) hu.le))
    have hdu : 0 < d u := sub_pos.mpr (hright u hcu)
    exact ⟨(mul_pos hwu hdu).ne', hc.trans hcu⟩
  have hp : 0 < ∫ u in Ioi (0 : ℝ), h u :=
    (setIntegral_pos_iff_support_of_nonneg_ae hn hi).2
      (lt_of_lt_of_le (by simp : 0 < volume (Ioi b)) (measure_mono hs))
  have hzero : (∫ u in Ioi (0 : ℝ), d u) = 0 := by
    dsimp [d]
    rw [integral_sub hf hg, hmass, sub_self]
  have he : (∫ u in Ioi (0 : ℝ), h u) =
      (∫ u in Ioi (0 : ℝ), w u*f u) -
        ∫ u in Ioi (0 : ℝ), w u*g u := by
    calc
      _ = ∫ u in Ioi (0 : ℝ), w u*d u-w c*d u := by
        apply integral_congr_ae
        exact Eventually.of_forall (fun u => by dsimp [h]; ring)
      _ = ∫ u in Ioi (0 : ℝ), w u*d u := by
        rw [integral_sub hwd (hd.const_mul (w c)), integral_const_mul,
          hzero, mul_zero, sub_zero]
      _ = ∫ u in Ioi (0 : ℝ), w u*f u-w u*g u := by
        apply integral_congr_ae
        exact Eventually.of_forall (fun u => by dsimp [d]; ring)
      _ = _ := integral_sub hwf hwg
  rw [he] at hp
  exact sub_pos.mp hp

end SingleCrossing
namespace ExponentialMoment

theorem power_exp_integrable (n : ℕ) :
    IntegrableOn (fun t : ℝ => t^n*Real.exp (-t)) (Ioi (0 : ℝ)) := by
  simpa only [Real.rpow_natCast, Real.rpow_one] using
    (integrableOn_rpow_mul_exp_neg_rpow (s := (n : ℝ)) (p := 1)
      (by have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n; linarith) (by norm_num))

theorem power_weighted_integrable {f : ℝ → ℝ} {A : ℝ} (n : ℕ)
    (hf : IntegrableOn f (Ioi (0 : ℝ)))
    (hb : ∀ t : ℝ, 0 ≤ t → ‖f t‖ ≤ A*Real.exp (-t)) :
    IntegrableOn (fun t : ℝ => t^n*f t) (Ioi (0 : ℝ)) := by
  have hm : AEStronglyMeasurable (fun t : ℝ => t^n*f t)
      (volume.restrict (Ioi (0 : ℝ))) :=
    (by fun_prop : Continuous (fun t : ℝ => t^n)).aestronglyMeasurable.mul
      hf.aestronglyMeasurable
  apply ((power_exp_integrable n).const_mul A).mono' hm
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht0 : 0 ≤ t := ht.le
  rw [norm_mul, Real.norm_of_nonneg (pow_nonneg ht0 n)]
  calc
    _ ≤ t^n*(A*Real.exp (-t)) :=
      mul_le_mul_of_nonneg_left (hb t ht0) (pow_nonneg ht0 n)
    _ = _ := by ring

end ExponentialMoment
#print axioms SingleCrossing.strict_integral_order_of_monotone_weight
#print axioms ExponentialMoment.power_exp_integrable
#print axioms ExponentialMoment.power_weighted_integrable
