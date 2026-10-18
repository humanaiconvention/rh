import RhDilationScalar001
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
Actual pointwise native multiplier control for compressed shift differences.
This is a form-topology bound, not operator-norm smallness and not an arithmetic
Schur-residual sign estimate. All frequencies use angular normalization.
-/
noncomputable section
namespace RhShiftFormMultiplier
open RhTail RhDilationScalar

lemma multiplier_mono_first {x y b : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (hb : 0 < b) :
    multiplier x b ≤ multiplier y b := by
  have hy : 0 ≤ y := hx.trans hxy
  unfold multiplier
  apply (div_le_div_iff₀ (by positivity : 0 < b * (b ^ 2 + x))
    (by positivity : 0 < b * (b ^ 2 + y))).mpr
  nlinarith [mul_nonneg (sub_nonneg.mpr hxy) (le_of_lt (mul_pos hb (sq_pos_of_pos hb)))]

lemma archMultiplier_nonneg {b omega : ℝ} (hb : 0 < b) :
    0 ≤ archMultiplier b omega := by
  exact tsum_nonneg (fun k => multiplier_nonneg (sq_nonneg omega) (by positivity))

/-- The ACTUAL complete multiplier is monotone in absolute angular frequency. -/
theorem archMultiplier_mono_abs {b omega xi : ℝ} (hb : 0 < b)
    (h : |omega| ≤ |xi|) : archMultiplier b omega ≤ archMultiplier b xi := by
  have hsq : omega ^ 2 ≤ xi ^ 2 := by
    nlinarith [sq_abs omega, sq_abs xi, abs_nonneg omega, abs_nonneg xi]
  apply Summable.tsum_le_tsum
    (fun k => multiplier_mono_first (sq_nonneg _) hsq (by positivity))
    (multiplier_series_summable_pos (sq_nonneg _) hb)
    (multiplier_series_summable_pos (sq_nonneg _) hb)

lemma low_cosine_difference {Omega omega : ℝ} (hOmega : 0 ≤ Omega)
    (homega : |omega| ≤ Omega) (ell ell' : ℝ) :
    |2 * (Real.cos (omega * ell') - Real.cos (omega * ell))| ≤
      2 * Omega * |ell' - ell| := by
  rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  have h := Real.abs_cos_sub_cos_le (omega * ell') (omega * ell)
  have heq : omega * ell' - omega * ell = omega * (ell' - ell) := by ring
  rw [heq, abs_mul] at h
  have hd := mul_le_mul_of_nonneg_right homega (abs_nonneg (ell' - ell))
  nlinarith

lemma universal_cosine_difference (omega ell ell' : ℝ) :
    |2 * (Real.cos (omega * ell') - Real.cos (omega * ell))| ≤ 4 := by
  have h1 := Real.neg_one_le_cos (omega * ell')
  have h2 := Real.cos_le_one (omega * ell')
  have h3 := Real.neg_one_le_cos (omega * ell)
  have h4 := Real.cos_le_one (omega * ell)
  apply abs_le.mpr
  constructor <;> linarith

/-- One bound covers the full frequency axis, with the exact native graph weight.
The high-frequency denominator is never replaced by a physical L2 bound. -/
theorem shift_graph_symbol_bound {b Omega : ℝ} (hb : 0 < b) (hOmega : 0 ≤ Omega)
    (omega ell ell' : ℝ) :
    |2 * (Real.cos (omega * ell') - Real.cos (omega * ell))| ≤
      (2 * Omega * |ell' - ell| + 4 / (1 + archMultiplier b Omega)) *
        (1 + archMultiplier b omega) := by
  have hw : 0 ≤ archMultiplier b omega := archMultiplier_nonneg hb
  have hO : 0 ≤ archMultiplier b Omega := archMultiplier_nonneg hb
  have hden : 0 < 1 + archMultiplier b Omega := by linarith
  have hfreq : 1 ≤ 1 + archMultiplier b omega := by linarith
  have hlow : 0 ≤ 2 * Omega * |ell' - ell| := by positivity
  have hhigh : 0 ≤ 4 / (1 + archMultiplier b Omega) := by positivity
  by_cases hl : |omega| ≤ Omega
  · have h := low_cosine_difference hOmega hl ell ell'
    calc
      _ ≤ 2 * Omega * |ell' - ell| := h
      _ ≤ (2 * Omega * |ell' - ell|) * (1 + archMultiplier b omega) := by
        nlinarith
      _ ≤ _ := by nlinarith
  · have hm : archMultiplier b Omega ≤ archMultiplier b omega := by
      apply archMultiplier_mono_abs hb
      rw [abs_of_nonneg hOmega]
      exact (le_of_not_ge hl)
    have hcost : 4 ≤ (4 / (1 + archMultiplier b Omega)) *
        (1 + archMultiplier b omega) := by
      have hmul := mul_le_mul_of_nonneg_left (show 1 + archMultiplier b Omega ≤
        1 + archMultiplier b omega by linarith) hhigh
      have heq : (4 / (1 + archMultiplier b Omega)) *
          (1 + archMultiplier b Omega) = 4 := by field_simp
      rw [heq] at hmul
      exact hmul
    exact (universal_cosine_difference omega ell ell').trans (by nlinarith)

end RhShiftFormMultiplier
#print axioms RhShiftFormMultiplier.archMultiplier_mono_abs
#print axioms RhShiftFormMultiplier.shift_graph_symbol_bound
