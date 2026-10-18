import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.Normed.Operator.NormedSpace

/-! Exact real polarization: a uniform diagonal bound for a symmetric
continuous bilinear form implies the same bilinear bound. This is a standard
Hilbert-space identity, not an arithmetic positivity or cancellation claim.
-/
noncomputable section
open scoped Topology
namespace RhSymmetricFormPolarization
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

theorem bilinear_bound_of_diagonal (B : V →L[ℝ] V →L[ℝ] ℝ)
    (hsym : ∀ x y : V, B x y = B y x) {eta : ℝ} (heta : 0 ≤ eta)
    (hdiag : ∀ x : V, |B x x| ≤ eta * ‖x‖^2) (x y : V) :
    |B x y| ≤ eta * ‖x‖ * ‖y‖ := by
  have hpol (a b : V) : 4 * B a b = B (a + b) (a + b) - B (a - b) (a - b) := by
    simp only [map_add, map_sub, ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply]
    rw [hsym b a]
    ring
  have hunit (a b : V) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) : |B a b| ≤ eta := by
    have hp := hdiag (a + b)
    have hm := hdiag (a - b)
    have ht := abs_sub (B (a + b) (a + b)) (B (a - b) (a - b))
    have hpar := parallelogram_law_with_norm ℝ a b
    rw [ha, hb] at hpar
    have hfour : |4 * B a b| = 4 * |B a b| := by rw [abs_mul]; norm_num
    rw [← hpol a b, hfour] at ht
    nlinarith
  by_cases hx : x = 0
  · subst x
    simp
  by_cases hy : y = 0
  · subst y
    simp
  have hnx : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have hny : ‖y‖ ≠ 0 := norm_ne_zero_iff.mpr hy
  let a := ‖x‖⁻¹ • x
  let b := ‖y‖⁻¹ • y
  have ha : ‖a‖ = 1 := by
    dsimp only [a]
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg x)), inv_mul_cancel₀ hnx]
  have hb : ‖b‖ = 1 := by
    dsimp only [b]
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg y)), inv_mul_cancel₀ hny]
  have hxa : ‖x‖ • a = x := by
    dsimp only [a]
    rw [smul_smul, mul_inv_cancel₀ hnx, one_smul]
  have hyb : ‖y‖ • b = y := by
    dsimp only [b]
    rw [smul_smul, mul_inv_cancel₀ hny, one_smul]
  calc
    |B x y| = |B (‖x‖ • a) (‖y‖ • b)| := by rw [hxa, hyb]
    _ = ‖x‖ * ‖y‖ * |B a b| := by
      simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul, abs_mul,
        abs_of_nonneg (norm_nonneg x), abs_of_nonneg (norm_nonneg y)]
      ring
    _ ≤ ‖x‖ * ‖y‖ * eta := mul_le_mul_of_nonneg_left (hunit a b ha hb)
      (mul_nonneg (norm_nonneg x) (norm_nonneg y))
    _ = _ := by ring

end RhSymmetricFormPolarization
#print axioms RhSymmetricFormPolarization.bilinear_bound_of_diagonal
