import ThetaStrictIncrease
import MacdonaldMass

/-! Actual complete theta profile has a finite positive half-line mass.
This file deliberately does not identify that integral with xi(1/2).
No arbitrary integral normalizer is called the source's arithmetic gamma0.
-/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology BigOperators
namespace ThetaMacdonald.Density

def thetaProfile (u : ℝ) : ℝ := ∑' k : ℕ, rawShell k u
def thetaMass : ℝ := ∫ u in Ioi (0 : ℝ), thetaProfile u
def thetaTailWeight (k : ℕ) : ℝ :=
  64 * Real.exp (-Real.pi * (k : ℝ)^2 / 4)
def thetaTailConstant : ℝ := ∑' k : ℕ, thetaTailWeight k

theorem rawShell_nonneg {u : ℝ} (hu : 0 ≤ u) (k : ℕ) :
    0 ≤ rawShell k u := by
  by_cases hk : k = 0
  · subst k
    rw [Series.rawShell_zero]
  · exact (rawShell_pos (by omega) hu).le

theorem rawShell_tail_bound {u : ℝ} (hu : 0 ≤ u) (k : ℕ) :
    ‖rawShell k u‖ ≤ thetaTailWeight k * Real.exp (-u) := by
  by_cases hk : k = 0
  · subst k
    rw [Series.rawShell_zero, norm_zero]
    unfold thetaTailWeight
    positivity
  have hkr : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (by omega : 1 ≤ k)
  have hks : (1 : ℝ) ≤ (k : ℝ)^2 := by nlinarith [sq_nonneg ((k : ℝ)-1)]
  let z := zArg k u
  have hz : 0 ≤ z := Series.zArg_nonneg k u
  have hp := Real.pow_div_factorial_le_exp (z/2) (by positivity : 0 ≤ z/2) 2
  norm_num at hp
  have hpoly : 8 * z^2 ≤ 64 * Real.exp (z/2) := by nlinarith
  have hpk : (3 : ℝ) ≤ Real.pi * (k : ℝ)^2 := by
    exact Real.pi_gt_three.le.trans
      (le_mul_of_one_le_right Real.pi_pos.le hks)
  have he := Real.add_one_le_exp (2*u)
  have he1 : 1 ≤ Real.exp (2*u) := Real.one_le_exp_iff.mpr (by linarith)
  have hzK : Real.pi * (k : ℝ)^2 ≤ z := by
    dsimp [z, zArg]
    exact le_mul_of_one_le_right (by positivity) he1
  have hz3 : 3 * Real.exp (2*u) ≤ z := by
    dsimp [z, zArg]
    exact mul_le_mul_of_nonneg_right hpk (Real.exp_pos _).le
  have hzu : 6*u ≤ z := by nlinarith
  calc
    ‖rawShell k u‖ = (8*z^2-12*z)*Real.exp (u/2-z) := by
      rw [Real.norm_of_nonneg (rawShell_nonneg hu k)]
      rfl
    _ ≤ (8*z^2)*Real.exp (u/2-z) := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      nlinarith
    _ ≤ (64*Real.exp (z/2))*Real.exp (u/2-z) :=
      mul_le_mul_of_nonneg_right hpoly (Real.exp_pos _).le
    _ = 64 * Real.exp (u/2-z/2) := by
      rw [mul_assoc, ← Real.exp_add]
      congr 2 <;> ring
    _ ≤ 64 * Real.exp (-Real.pi*(k:ℝ)^2/4-u) := by
      apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by norm_num)
      nlinarith
    _ = thetaTailWeight k * Real.exp (-u) := by
      unfold thetaTailWeight
      rw [sub_eq_add_neg, Real.exp_add]
      ring

theorem summable_thetaTailWeight : Summable thetaTailWeight := by
  have h := (HurwitzKernelBounds.summable_f_nat 0 0
    (by norm_num : (0 : ℝ) < 1/4)).mul_left 64
  convert h using 1
  funext k
  simp only [thetaTailWeight, HurwitzKernelBounds.f_nat, pow_zero, one_mul, add_zero]
  congr 2 <;> ring

theorem thetaProfile_tail_bound {u : ℝ} (hu : 0 ≤ u) :
    ‖thetaProfile u‖ ≤ thetaTailConstant * Real.exp (-u) := by
  have hs := Series.summable_rawShell u
  calc
    ‖thetaProfile u‖ ≤ ∑' k : ℕ, ‖rawShell k u‖ :=
      norm_tsum_le_tsum_norm hs.norm
    _ ≤ ∑' k : ℕ, thetaTailWeight k * Real.exp (-u) :=
      hs.norm.tsum_mono (summable_thetaTailWeight.mul_right _)
        (fun k => rawShell_tail_bound hu k)
    _ = thetaTailConstant * Real.exp (-u) :=
      summable_thetaTailWeight.tsum_mul_right _

theorem thetaProfile_pos {u : ℝ} (hu : 0 ≤ u) :
    0 < thetaProfile u :=
  (Series.summable_rawShell u).tsum_pos (rawShell_nonneg hu) 1
    (rawShell_pos (by norm_num) hu)

theorem integrable_thetaProfile :
    IntegrableOn thetaProfile (Ioi (0 : ℝ)) := by
  have hc : Continuous thetaProfile :=
    continuous_iff_continuousAt.mpr (fun u =>
      (Series.hasDerivAt_tsum_rawShell u).continuousAt)
  apply ((integrableOn_exp_neg_Ioi 0).const_mul thetaTailConstant).mono'
    hc.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  exact thetaProfile_tail_bound hu.le

theorem thetaMass_pos : 0 < thetaMass := by
  have hn : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] thetaProfile := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact (thetaProfile_pos hu.le).le
  apply (setIntegral_pos_iff_support_of_nonneg_ae hn integrable_thetaProfile).2
  have hs : Function.support thetaProfile ∩ Ioi (0 : ℝ) = Ioi (0 : ℝ) := by
    ext u
    constructor
    · exact fun h => h.2
    · intro hu
      exact ⟨(thetaProfile_pos hu.le).ne', hu⟩
  rw [hs]
  simp

end ThetaMacdonald.Density
#print axioms ThetaMacdonald.Density.rawShell_tail_bound
#print axioms ThetaMacdonald.Density.summable_thetaTailWeight
#print axioms ThetaMacdonald.Density.thetaProfile_tail_bound
#print axioms ThetaMacdonald.Density.thetaProfile_pos
#print axioms ThetaMacdonald.Density.integrable_thetaProfile
#print axioms ThetaMacdonald.Density.thetaMass_pos
