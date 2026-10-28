import ThetaMassBounds
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-! Actual positive-index Gaussian seed and its improper FTC identity.
The origin term and the endpoint derivative limit are both proved, not assumed. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology BigOperators
namespace ThetaMacdonald.Mass
open Symmetry Density

def seedTail (u : ℝ) : ℝ := gaussianSum u - Real.exp (u/2)
def seedTailD1 (u : ℝ) : ℝ :=
  (∑' k : ℕ, gaussianSeedD1 k u) - (1/2 : ℝ)*Real.exp (u/2)
def seedTailD2 (u : ℝ) : ℝ :=
  (∑' k : ℕ, gaussianSeedD2 k u) - (1/4 : ℝ)*Real.exp (u/2)
def tailC : ℝ := ∑' k : ℕ, thetaTailWeight (k+1)

theorem seedTail_eq_tsum (u : ℝ) :
    seedTail u = ∑' k : ℕ, gaussianSeed (k+1) u := by
  have h := (summable_gaussianSeed u).tsum_eq_zero_add
  rw [gaussianSeed_zero] at h
  dsimp [seedTail, gaussianSum]
  linarith

theorem seedTailD1_eq_tsum (u : ℝ) :
    seedTailD1 u = ∑' k : ℕ, gaussianSeedD1 (k+1) u := by
  have h := (summable_gaussianSeedD1 u).tsum_eq_zero_add
  have h0 : gaussianSeedD1 0 u = (1/2 : ℝ)*Real.exp (u/2) := by
    simp [gaussianSeedD1, gaussianSeed, zArg]
  rw [h0] at h
  dsimp [seedTailD1]
  linarith

theorem hasDerivAt_seedTail (u : ℝ) :
    HasDerivAt seedTail (seedTailD1 u) u := by
  convert (hasDerivAt_tsum_gaussianSeed u).sub
    ((hasDerivAt_id u).div_const 2).exp using 1
  · rfl
  · dsimp [seedTailD1]; ring

theorem hasDerivAt_seedTailD1 (u : ℝ) :
    HasDerivAt seedTailD1 (seedTailD2 u) u := by
  convert (hasDerivAt_tsum_gaussianSeedD1 u).sub
    (((hasDerivAt_id u).div_const 2).exp.const_mul (1/2 : ℝ)) using 1
  · rfl
  · dsimp [seedTailD2]; ring

theorem raw_eq_seedTail (u : ℝ) :
    thetaProfile u = 2*seedTailD2 u - (1/2 : ℝ)*seedTail u := by
  unfold thetaProfile
  rw [raw_sum_eq_centeredTheta, second_deriv_centeredTheta]
  dsimp [centeredThetaD2, centeredTheta, gaussianSum, seedTailD2, seedTail]
  ring

theorem seedTailD1_origin : seedTailD1 0 = -(1/4 : ℝ) := by
  have h0 := Reflection.deriv_zero_of_even centeredTheta_even
  have h : centeredThetaD1 0 = 0 :=
    (hasDerivAt_centeredTheta 0).deriv.symm.trans h0
  simp only [centeredThetaD1, zero_div, Real.exp_zero, mul_one] at h
  dsimp [seedTailD1]
  simp only [zero_div, Real.exp_zero, mul_one]
  linarith

theorem seed_decay_data {u : ℝ} (hu : 0 ≤ u) {k : ℕ} (hk : 1 ≤ k) :
    let z := zArg k u
    3 ≤ z ∧ u/2-z/2 ≤ -Real.pi*(k:ℝ)^2/4-u := by
  have hkr : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hks : (1 : ℝ) ≤ (k : ℝ)^2 := by nlinarith [sq_nonneg ((k:ℝ)-1)]
  have hpk : (3 : ℝ) ≤ Real.pi*(k:ℝ)^2 :=
    Real.pi_gt_three.le.trans (le_mul_of_one_le_right Real.pi_pos.le hks)
  have he := Real.add_one_le_exp (2*u)
  have he1 : 1 ≤ Real.exp (2*u) := Real.one_le_exp_iff.mpr (by linarith)
  have hzK : Real.pi*(k:ℝ)^2 ≤ zArg k u := by
    unfold zArg
    exact le_mul_of_one_le_right (by positivity) he1
  have hz3 : 3*Real.exp (2*u) ≤ zArg k u := by
    unfold zArg
    exact mul_le_mul_of_nonneg_right hpk (Real.exp_pos _).le
  constructor <;> nlinarith

theorem seed_tail_bound {u : ℝ} (hu : 0 ≤ u) {k : ℕ} (hk : 1 ≤ k) :
    ‖gaussianSeed k u‖ ≤ thetaTailWeight k * Real.exp (-u) := by
  obtain ⟨hz, he⟩ := seed_decay_data hu hk
  have he' : u/2-zArg k u ≤ -Real.pi*(k:ℝ)^2/4-u := by linarith
  rw [gaussianSeed, Real.norm_of_nonneg (Real.exp_pos _).le]
  calc
    _ ≤ Real.exp (-Real.pi*(k:ℝ)^2/4-u) := Real.exp_le_exp.mpr he'
    _ ≤ 64 * Real.exp (-Real.pi*(k:ℝ)^2/4-u) := by
      nlinarith [Real.exp_pos (-Real.pi*(k:ℝ)^2/4-u)]
    _ = thetaTailWeight k * Real.exp (-u) := by
      unfold thetaTailWeight
      rw [sub_eq_add_neg, Real.exp_add]
      ring

theorem seedD1_tail_bound {u : ℝ} (hu : 0 ≤ u) {k : ℕ} (hk : 1 ≤ k) :
    ‖gaussianSeedD1 k u‖ ≤ thetaTailWeight k * Real.exp (-u) := by
  obtain ⟨hz, he⟩ := seed_decay_data hu hk
  have hp := Real.add_one_le_exp (zArg k u/2)
  have hpoly : 2*zArg k u - 1/2 ≤ 64*Real.exp (zArg k u/2) := by
    nlinarith [Real.exp_pos (zArg k u/2)]
  rw [gaussianSeedD1, norm_mul, Real.norm_eq_abs,
    abs_of_nonpos (by linarith : (1/2 : ℝ)-2*zArg k u ≤ 0),
    gaussianSeed, Real.norm_of_nonneg (Real.exp_pos _).le]
  calc
    _ ≤ (64*Real.exp (zArg k u/2))*Real.exp (u/2-zArg k u) :=
      mul_le_mul_of_nonneg_right (by linarith : -((1/2 : ℝ)-2*zArg k u) ≤ _) (Real.exp_pos _).le
    _ = 64*Real.exp (u/2-zArg k u/2) := by
      rw [mul_assoc, ← Real.exp_add]; congr 2 <;> ring
    _ ≤ 64*Real.exp (-Real.pi*(k:ℝ)^2/4-u) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) (by norm_num)
    _ = thetaTailWeight k * Real.exp (-u) := by
      unfold thetaTailWeight
      rw [sub_eq_add_neg, Real.exp_add]
      ring

theorem shifted_sum_bound {f : ℕ → ℝ} (hf : Summable f) {u : ℝ}
    (hb : ∀ k : ℕ, ‖f (k+1)‖ ≤ thetaTailWeight (k+1)*Real.exp (-u)) :
    ‖∑' k : ℕ, f (k+1)‖ ≤ tailC*Real.exp (-u) := by
  have hs : Summable (fun k : ℕ => f (k+1)) := by
    simpa only [Function.comp_def, Nat.succ_eq_add_one] using
      hf.comp_injective Nat.succ_injective
  have hw : Summable (fun k : ℕ => thetaTailWeight (k+1)) := by
    simpa only [Function.comp_def, Nat.succ_eq_add_one] using
      summable_thetaTailWeight.comp_injective Nat.succ_injective
  calc
    _ ≤ ∑' k : ℕ, ‖f (k+1)‖ := norm_tsum_le_tsum_norm hs.norm
    _ ≤ ∑' k : ℕ, thetaTailWeight (k+1)*Real.exp (-u) :=
      hs.norm.tsum_mono (hw.mul_right _) hb
    _ = tailC*Real.exp (-u) := hw.tsum_mul_right _

theorem seedTail_bound {u : ℝ} (hu : 0 ≤ u) :
    ‖seedTail u‖ ≤ tailC*Real.exp (-u) := by
  rw [seedTail_eq_tsum]
  exact shifted_sum_bound (summable_gaussianSeed u)
    (fun k => seed_tail_bound hu (by omega))

theorem seedTailD1_bound {u : ℝ} (hu : 0 ≤ u) :
    ‖seedTailD1 u‖ ≤ tailC*Real.exp (-u) := by
  rw [seedTailD1_eq_tsum]
  exact shifted_sum_bound (summable_gaussianSeedD1 u)
    (fun k => seedD1_tail_bound hu (by omega))

theorem integrable_seedTail : IntegrableOn seedTail (Ioi (0 : ℝ)) := by
  have hc : Continuous seedTail :=
    continuous_iff_continuousAt.mpr (fun u => (hasDerivAt_seedTail u).continuousAt)
  apply ((integrableOn_exp_neg_Ioi 0).const_mul tailC).mono' hc.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  exact seedTail_bound hu.le

theorem seedTailD1_tendsto_zero : Tendsto seedTailD1 atTop (𝓝 0) := by
  apply squeeze_zero_norm' (by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with u hu
    exact seedTailD1_bound hu)
  simpa only [Function.comp_def, mul_zero] using
    (Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot).const_mul tailC

theorem integrable_seedTailD2 : IntegrableOn seedTailD2 (Ioi (0 : ℝ)) := by
  have heq : seedTailD2 = fun u => thetaProfile u/2 + seedTail u/4 := by
    funext u
    have h := raw_eq_seedTail u
    linarith
  rw [heq]
  exact (integrable_thetaProfile.div_const 2).add (integrable_seedTail.div_const 4)

theorem integral_seedTailD2 :
    (∫ u in Ioi (0 : ℝ), seedTailD2 u) = (1/4 : ℝ) := by
  have h := integral_Ioi_of_hasDerivAt_of_tendsto' (a := (0 : ℝ)) (m := (0 : ℝ))
    (fun u _ => hasDerivAt_seedTailD1 u) integrable_seedTailD2 seedTailD1_tendsto_zero
  simpa only [seedTailD1_origin, sub_neg_eq_add, zero_add] using h

theorem thetaMass_improper_FTC :
    thetaMass = 1/2 - (1/2 : ℝ)*(∫ u in Ioi (0 : ℝ), seedTail u) := by
  unfold thetaMass
  have heq : thetaProfile = fun u => 2*seedTailD2 u - (1/2 : ℝ)*seedTail u :=
    funext raw_eq_seedTail
  rw [heq, integral_sub (integrable_seedTailD2.const_mul 2)
    (integrable_seedTail.const_mul (1/2 : ℝ)), integral_const_mul, integral_const_mul,
    integral_seedTailD2]
  ring

end ThetaMacdonald.Mass
#print axioms ThetaMacdonald.Mass.seedTailD1_origin
#print axioms ThetaMacdonald.Mass.integrable_seedTail
#print axioms ThetaMacdonald.Mass.seedTailD1_tendsto_zero
#print axioms ThetaMacdonald.Mass.integrable_seedTailD2
#print axioms ThetaMacdonald.Mass.integral_seedTailD2
#print axioms ThetaMacdonald.Mass.thetaMass_improper_FTC
