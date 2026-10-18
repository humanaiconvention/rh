import RhShiftFormMultiplier001
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! Exact form-topology continuity of each native compressed translation symbol.
The high-frequency weight is the complete native multiplier, not an assumed
Sobolev estimate. No positivity of the signed arithmetic residual is asserted. -/
noncomputable section
open Filter
open scoped Topology
namespace RhShiftFormContinuity
open RhTail RhDilationScalar RhShiftFormMultiplier

lemma multiplier_antitone_second {x b c : ℝ} (hx : 0 ≤ x) (hb : 0 < b)
    (hbc : b ≤ c) : multiplier x c ≤ multiplier x b := by
  have hc : 0 < c := hb.trans_le hbc
  have hpow : b ^ 2 ≤ c ^ 2 := by nlinarith
  have hden : b * (b ^ 2 + x) ≤ c * (c ^ 2 + x) := by gcongr
  exact div_le_div_of_nonneg_left (by positivity : 0 ≤ 2 * x)
    (by positivity : 0 < b * (b ^ 2 + x)) hden

lemma archMultiplier_antitone_index {b c : ℝ} (hb : 0 < b) (hbc : b ≤ c)
    (omega : ℝ) : archMultiplier c omega ≤ archMultiplier b omega := by
  have hc : 0 < c := hb.trans_le hbc
  apply Summable.tsum_le_tsum
    (fun k => multiplier_antitone_second (sq_nonneg _) (by positivity) (by linarith))
    (multiplier_series_summable_pos (sq_nonneg _) hc)
    (multiplier_series_summable_pos (sq_nonneg _) hb)

/-- This uses the already compiled trapezoid theorem at 5/2, inside its actual
proved b>=1 range, then compares it to the native b=1/2 multiplier. -/
theorem native_log_lower (omega : ℝ) :
    (1 / 2 : ℝ) * Real.log (1 + omega ^ 2 / (5 / 2 : ℝ) ^ 2) ≤
      archMultiplier (1 / 2) omega := by
  have ht := infinite_tail_trapezoid (sq_nonneg omega)
    (by norm_num : (1 : ℝ) ≤ 5 / 2)
  have hn := multiplier_nonneg (sq_nonneg omega) (by norm_num : (0 : ℝ) < 5 / 2)
  have hm := archMultiplier_antitone_index (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num : (1 / 2 : ℝ) ≤ 5 / 2) omega
  unfold archMultiplier at hm ⊢
  linarith

/-- A proved divergence of the native graph weight, not a numerical observation. -/
theorem native_multiplier_atTop :
    Tendsto (archMultiplier (1 / 2)) atTop atTop := by
  have hp : Tendsto (fun x : ℝ => x ^ 2 / (5 / 2 : ℝ) ^ 2) atTop atTop :=
    (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).atTop_div_const (by norm_num)
  have ha : Tendsto (fun x : ℝ => 1 + x ^ 2 / (5 / 2 : ℝ) ^ 2) atTop atTop :=
    tendsto_atTop_add_const_left atTop 1 hp
  have hl := (Real.tendsto_log_atTop.comp ha).const_mul_atTop
    (by norm_num : (0 : ℝ) < 1 / 2)
  exact tendsto_atTop_mono (fun x => native_log_lower x) hl

/-- Any prescribed positive form-error budget can be met uniformly in angular
frequency by taking the two shift lengths sufficiently close. -/
theorem uniform_native_shift_budget {eta : ℝ} (heta : 0 < eta) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ (ell ell' omega : ℝ), |ell' - ell| < delta →
      |2 * (Real.cos (omega * ell') - Real.cos (omega * ell))| <
        eta * (1 + archMultiplier (1 / 2) omega) := by
  have hlarge : ∀ᶠ x : ℝ in atTop, 8 / eta < archMultiplier (1 / 2) x :=
    native_multiplier_atTop.eventually (eventually_gt_atTop (8 / eta))
  obtain ⟨Omega, hOmega, hm⟩ :=
    ((eventually_gt_atTop (0 : ℝ)).and hlarge).exists
  have hden : 0 < 1 + archMultiplier (1 / 2) Omega := by
    have hn := archMultiplier_nonneg (b := 1 / 2) (omega := Omega) (by norm_num)
    linarith
  have hhigh : 4 / (1 + archMultiplier (1 / 2) Omega) < eta / 2 := by
    apply (div_lt_iff₀ hden).mpr
    have hmul : 8 < eta * archMultiplier (1 / 2) Omega :=
      by simpa only [mul_comm] using (div_lt_iff₀ heta).mp hm
    nlinarith
  refine ⟨eta / (4 * Omega), by positivity, ?_⟩
  intro ell ell' omega hshift
  have hlow : 2 * Omega * |ell' - ell| < eta / 2 := by
    have hh := (lt_div_iff₀ (by positivity : 0 < 4 * Omega)).mp hshift
    nlinarith
  have hbound := shift_graph_symbol_bound (by norm_num : (0 : ℝ) < 1 / 2)
    hOmega.le omega ell ell'
  have hweight : 0 < 1 + archMultiplier (1 / 2) omega := by
    have hn := archMultiplier_nonneg (b := 1 / 2) (omega := omega) (by norm_num)
    linarith
  exact hbound.trans_lt (mul_lt_mul_of_pos_right (by linarith) hweight)

end RhShiftFormContinuity
#print axioms RhShiftFormContinuity.native_log_lower
#print axioms RhShiftFormContinuity.native_multiplier_atTop
#print axioms RhShiftFormContinuity.uniform_native_shift_budget
