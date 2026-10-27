import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The finite-prefix cumulative square-energy identity

Arbitrary real coefficients at finitely many positive sites are allowed.
The inclusive prefix convention gives the compensated function a right
derivative even at a jump. The proof uses the existing right-sided FTC,
not continuity plus an almost-everywhere derivative alone.
-/

open Set Filter MeasureTheory
open scoped BigOperators Topology

namespace CumulativeSquareEnergy

noncomputable section

variable {ι : Type*}

def prefixMass (s : Finset ι) (p c : ι → ℝ) (t : ℝ) : ℝ :=
  ∑ i ∈ s, if p i ≤ t then c i else 0

def weightedPrefix (s : Finset ι) (p c : ι → ℝ) (t : ℝ) : ℝ :=
  prefixMass s p (fun i => c i / p i) t

def compensated (s : Finset ι) (p c : ι → ℝ) (t : ℝ) : ℝ :=
  weightedPrefix s p c t - prefixMass s p c t / t

def atomCompensated (p c t : ℝ) : ℝ :=
  if p ≤ t then c / p - c / t else 0

theorem compensated_eq_sum (s : Finset ι) (p c : ι → ℝ) (t : ℝ) :
    compensated s p c t = ∑ i ∈ s, atomCompensated (p i) (c i) t := by
  unfold compensated weightedPrefix prefixMass
  rw [Finset.sum_div, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases h : p i ≤ t <;> simp [atomCompensated, h]

theorem atomCompensated_eq_max {p c t : ℝ} (hp : 0 < p) (ht : 0 < t) :
    atomCompensated p c t = c * max (t - p) 0 / (p * t) := by
  by_cases h : p ≤ t
  · rw [atomCompensated, ite_eq_left h, max_eq_left (sub_nonneg.mpr h)]
    field_simp [hp.ne', ht.ne']
  · have htp : t - p ≤ 0 := sub_nonpos.mpr (le_of_not_ge h)
    simp [atomCompensated, h, max_eq_right htp]

theorem atomCompensated_continuousOn {p c : ℝ} (hp : 0 < p) :
    ContinuousOn (atomCompensated p c) (Ioi 0) := by
  have hmax : ContinuousOn (fun t : ℝ => c * max (t - p) 0 / (p * t)) (Ioi 0) :=
    (continuousOn_const.mul
      (((continuous_id.sub continuous_const).max continuous_const).continuousOn)).div
      (continuousOn_const.mul continuousOn_id)
      (fun t ht => mul_ne_zero hp.ne' (ne_of_gt ht))
  apply hmax.congr
  intro t ht
  exact atomCompensated_eq_max hp ht

theorem atomCompensated_hasDeriv_right {p c t : ℝ} (ht : 0 < t) :
    HasDerivWithinAt (atomCompensated p c)
      (if p ≤ t then c / t ^ 2 else 0) (Ioi t) t := by
  by_cases h : p ≤ t
  · rw [ite_eq_left h]
    have hd : HasDerivAt (fun x : ℝ => c / p - c / x) (c / t ^ 2) t := by
      have hd0 := (hasDerivAt_const t (c / p)).fun_sub
        ((hasDerivAt_const t c).fun_div (hasDerivAt_id t) ht.ne')
      simpa only [id_eq, zero_mul, mul_one, zero_sub, neg_div, neg_neg] using hd0
    apply hd.hasDerivWithinAt.congr
    · intro x hx
      simp [atomCompensated, h.trans hx.le]
    · simp [atomCompensated, h]
  · rw [ite_eq_right h]
    have hev : ∀ᶠ x in 𝓝[Ioi t] t, x < p :=
      (eventually_lt_nhds (lt_of_not_ge h)).filter_mono nhdsWithin_le_nhds
    apply (hasDerivWithinAt_const t (Ioi t) (0 : ℝ)).congr_of_eventuallyEq
    · filter_upwards [hev] with x hx
      simp [atomCompensated, not_le.mpr hx]
    · simp [atomCompensated, h]

theorem compensated_continuousOn (s : Finset ι) (p c : ι → ℝ)
    (hp : ∀ i ∈ s, 0 < p i) : ContinuousOn (compensated s p c) (Ioi 0) := by
  have hc : ContinuousOn (fun t => ∑ i ∈ s, atomCompensated (p i) (c i) t) (Ioi 0) :=
    continuousOn_finsetSum s fun i hi => atomCompensated_continuousOn (hp i hi)
  exact hc.congr fun t ht => compensated_eq_sum s p c t

theorem compensated_hasDeriv_right (s : Finset ι) (p c : ι → ℝ) {t : ℝ}
    (ht : 0 < t) : HasDerivWithinAt (compensated s p c)
      (prefixMass s p c t / t ^ 2) (Ioi t) t := by
  have hd := HasDerivWithinAt.fun_sum (u := s)
    (fun i hi => atomCompensated_hasDeriv_right (p := p i) (c := c i) ht)
  have heq : (∑ i ∈ s, if p i ≤ t then c i / t ^ 2 else 0) =
      prefixMass s p c t / t ^ 2 := by
    unfold prefixMass
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases h : p i ≤ t <;> simp [h]
  rw [heq] at hd
  exact hd.congr (fun x hx => compensated_eq_sum s p c x) (compensated_eq_sum s p c t)

theorem prefixMass_measurable (s : Finset ι) (p c : ι → ℝ) :
    Measurable (prefixMass s p c) := by
  unfold prefixMass
  apply Finset.measurable_sum
  intro i hi
  change Measurable ((Ici (p i)).indicator (fun _ : ℝ => c i))
  exact measurable_const.indicator measurableSet_Ici

theorem prefixMass_norm_le (s : Finset ι) (p c : ι → ℝ) (t : ℝ) :
    ‖prefixMass s p c t‖ ≤ ∑ i ∈ s, ‖c i‖ := by
  unfold prefixMass
  calc
    _ ≤ ∑ i ∈ s, ‖if p i ≤ t then c i else 0‖ := norm_sum_le _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro i hi
      by_cases h : p i ≤ t <;> simp [h]

theorem prefixMass_sq_intervalIntegrable (s : Finset ι) (p c : ι → ℝ)
    {a b : ℝ} (hab : a ≤ b) :
    IntervalIntegrable (fun t => prefixMass s p c t ^ 2) volume a b := by
  apply (intervalIntegrable_iff_integrableOn_Icc_of_le hab).2
  apply Measure.integrableOn_of_bounded (measure_Icc_lt_top.ne)
    ((prefixMass_measurable s p c).pow_const 2).aestronglyMeasurable
  filter_upwards with t
  rw [norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (prefixMass_norm_le s p c t) 2

/-- A useful analytic interface, using a right derivative everywhere in the
interior and explicit integrability, rather than an a.e. FTC shortcut. -/
theorem square_energy_of_right_derivative {g M γ : ℝ → ℝ} {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hc : ContinuousOn γ (Icc a b))
    (hd : ∀ t ∈ Ioo a b, HasDerivWithinAt γ (M t / t ^ 2) (Ioi t) t)
    (hg : ∀ t ∈ Icc a b, g t = γ t + M t / t)
    (hgi : IntervalIntegrable (fun t => g t ^ 2) volume a b)
    (hMi : IntervalIntegrable (fun t => M t ^ 2 / t ^ 2) volume a b) :
    (∫ t in a..b, g t ^ 2) = b * γ b ^ 2 - a * γ a ^ 2 +
      ∫ t in a..b, M t ^ 2 / t ^ 2 := by
  have hFcont : ContinuousOn (fun t => t * γ t ^ 2) (Icc a b) :=
    continuousOn_id.mul (hc.pow 2)
  have hFderiv : ∀ t ∈ Ioo a b, HasDerivWithinAt (fun t => t * γ t ^ 2)
      (g t ^ 2 - M t ^ 2 / t ^ 2) (Ioi t) t := by
    intro t ht
    have ht0 : t ≠ 0 := ne_of_gt (ha.trans ht.1)
    have hgt := hg t ⟨ht.1.le, ht.2.le⟩
    have hbase : HasDerivWithinAt (fun x => x * γ x ^ 2)
        (γ t ^ 2 + t * (2 * γ t * (M t / t ^ 2))) (Ioi t) t := by
      simpa using
        (hasDerivWithinAt_id t (Ioi t)).fun_mul ((hd t ht).fun_pow 2)
    apply hbase.congr_deriv
    rw [hgt]
    field_simp [ht0]
    ring
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le
    hab hFcont hFderiv (hgi.sub hMi)
  rw [intervalIntegral.integral_sub hgi hMi] at hFTC
  linarith

/-- The finite-prefix square-energy identity at arbitrary real endpoints,
including endpoints and interiors at prefix jumps. -/
theorem finite_prefix_square_energy (s : Finset ι) (p c : ι → ℝ)
    (hp : ∀ i ∈ s, 0 < p i) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ t in a..b, weightedPrefix s p c t ^ 2) =
      b * compensated s p c b ^ 2 - a * compensated s p c a ^ 2 +
        ∫ t in a..b, prefixMass s p c t ^ 2 / t ^ 2 := by
  have hgi := prefixMass_sq_intervalIntegrable s p (fun i => c i / p i) hab
  have hmi := prefixMass_sq_intervalIntegrable s p c hab
  have hinv : ContinuousOn (fun t : ℝ => 1 / t ^ 2) (uIcc a b) := by
    apply continuousOn_const.div (continuousOn_id.pow 2)
    intro t ht
    rw [uIcc_of_le hab] at ht
    exact pow_ne_zero 2 (ne_of_gt (ha.trans_le ht.1))
  have hMi : IntervalIntegrable (fun t => prefixMass s p c t ^ 2 / t ^ 2) volume a b := by
    simpa only [div_eq_mul_inv, one_mul] using hmi.mul_continuousOn hinv
  apply square_energy_of_right_derivative ha hab
    ((compensated_continuousOn s p c hp).mono (fun t ht => ha.trans_le ht.1))
    (fun t ht => compensated_hasDeriv_right s p c (ha.trans ht.1))
    (fun t ht => ?_) hgi hMi
  unfold compensated weightedPrefix
  ring

/-- The original positive-integer finite-prefix specialization. Index zero
is excluded explicitly, so no totalized division by zero is concealed. -/
theorem nat_prefix_square_energy (N : ℕ) (c : ℕ → ℝ) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) :
    (∫ t in a..b, weightedPrefix (Finset.Icc 1 N) (fun n => (n : ℝ)) c t ^ 2) =
      b * compensated (Finset.Icc 1 N) (fun n => (n : ℝ)) c b ^ 2 -
      a * compensated (Finset.Icc 1 N) (fun n => (n : ℝ)) c a ^ 2 +
        ∫ t in a..b, prefixMass (Finset.Icc 1 N) (fun n => (n : ℝ)) c t ^ 2 / t ^ 2 := by
  apply finite_prefix_square_energy _ _ _ ?_ ha hab
  intro n hn
  exact_mod_cast (Nat.succ_le_iff.mp (Finset.mem_Icc.mp hn).1)

/-- A genuine jump-endpoint instantiation: no derivative across the left
side of the positive atom is assumed, and its compensated value is zero. -/
theorem single_atom_left_endpoint {q c b : ℝ} (hq : 0 < q) (hqb : q ≤ b) :
    (∫ t in q..b, weightedPrefix ({0} : Finset ℕ) (fun _ => q) (fun _ => c) t ^ 2) =
      b * (c / q - c / b) ^ 2 +
        ∫ t in q..b, prefixMass ({0} : Finset ℕ) (fun _ => q) (fun _ => c) t ^ 2 / t ^ 2 := by
  have h := finite_prefix_square_energy ({0} : Finset ℕ) (fun _ => q) (fun _ => c)
    (fun i hi => hq) hq hqb
  have hleft : compensated ({0} : Finset ℕ) (fun _ => q) (fun _ => c) q = 0 := by
    simp [compensated, weightedPrefix, prefixMass]
  have hright : compensated ({0} : Finset ℕ) (fun _ => q) (fun _ => c) b = c / q - c / b := by
    simp [compensated, weightedPrefix, prefixMass, hqb]
  rw [hleft, hright] at h
  simpa only [zero_pow (by decide : 2 ≠ 0), mul_zero, sub_zero] using h

end
end CumulativeSquareEnergy

#print axioms CumulativeSquareEnergy.compensated_continuousOn
#print axioms CumulativeSquareEnergy.compensated_hasDeriv_right
#print axioms CumulativeSquareEnergy.square_energy_of_right_derivative
#print axioms CumulativeSquareEnergy.finite_prefix_square_energy
#print axioms CumulativeSquareEnergy.nat_prefix_square_energy
#print axioms CumulativeSquareEnergy.single_atom_left_endpoint
