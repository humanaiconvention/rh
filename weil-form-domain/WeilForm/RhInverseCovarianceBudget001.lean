import RhCoerciveSchurInverse001

/-! Quantitative norm and mixed covariance control for the SAME constructed
coercive inverse. No components of a source vector are separated. The positive
coercivity constant is explicit; this lemma does not establish such a gap.
-/
noncomputable section
open scoped Topology
namespace RhInverseCovarianceBudget
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

lemma inverse_norm_le (B : V →L[ℝ] V →L[ℝ] ℝ) (hB : IsCoercive B)
    {g : ℝ} (hg : 0 < g) (hco : ∀ q : V, g * ‖q‖^2 ≤ B q q) (b : V) :
    ‖RhCoerciveSchurInverse.inverse B hB b‖ ≤ ‖b‖ / g := by
  let z := RhCoerciveSchurInverse.inverse B hB b
  have hz : g * ‖z‖^2 ≤ inner ℝ b z := by
    calc
      _ ≤ B z z := hco z
      _ = _ := RhCoerciveSchurInverse.inverse_weak_equation B hB b z
  have hcs := real_inner_le_norm b z
  change ‖z‖ ≤ ‖b‖ / g
  apply (le_div_iff₀ hg).mpr
  by_cases hn : ‖z‖ = 0
  · rw [hn, zero_mul]
    exact norm_nonneg b
  · have hp : 0 < ‖z‖ := lt_of_le_of_ne (norm_nonneg z) (Ne.symm hn)
    apply (mul_le_mul_iff_right₀ hp).mp
    nlinarith

/-- Exact common inverse; the bound covers mixed off-diagonal covariances. -/
theorem mixed_inverse_bound (B : V →L[ℝ] V →L[ℝ] ℝ) (hB : IsCoercive B)
    {g : ℝ} (hg : 0 < g) (hco : ∀ q : V, g * ‖q‖^2 ≤ B q q) (b c : V) :
    |inner ℝ b (RhCoerciveSchurInverse.inverse B hB c)| ≤ ‖b‖ * ‖c‖ / g := by
  calc
    _ ≤ ‖b‖ * ‖RhCoerciveSchurInverse.inverse B hB c‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖b‖ * (‖c‖ / g) :=
      mul_le_mul_of_nonneg_left (inverse_norm_le B hB hg hco c) (norm_nonneg b)
    _ = _ := by ring

/-- Quadratic budget after WHOLE-source norm control, retaining every native
cross covariance inside each source and the single common inverse. -/
theorem quadratic_covariance_bound (B : V →L[ℝ] V →L[ℝ] ℝ) (hB : IsCoercive B)
    {g eta x y : ℝ} (hg : 0 < g) (heta : 0 ≤ eta) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hco : ∀ q : V, g * ‖q‖^2 ≤ B q q) (b c : V)
    (hb : ‖b‖ ≤ eta * x) (hc : ‖c‖ ≤ eta * y) :
    |inner ℝ b (RhCoerciveSchurInverse.inverse B hB c)| ≤ eta^2 * x * y / g := by
  have hm : ‖b‖ * ‖c‖ ≤ eta^2 * x * y := by
    have h := mul_le_mul hb hc (norm_nonneg c) (mul_nonneg heta hx)
    nlinarith
  exact (mixed_inverse_bound B hB hg hco b c).trans
    ((div_le_div_iff_of_pos_right hg).mpr hm)

end RhInverseCovarianceBudget
#print axioms RhInverseCovarianceBudget.inverse_norm_le
#print axioms RhInverseCovarianceBudget.mixed_inverse_bound
#print axioms RhInverseCovarianceBudget.quadratic_covariance_bound
