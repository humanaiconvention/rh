import RhCenteredPrimitiveApproximation001

/-! Physical scalar mass convergence is deduced from actual L2 errors.
No convergence of the complete form is assumed here.
-/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace RhPhysicalMassConvergence
open RhAnchored

lemma totalMass_sub {R : ℝ} {f g : ℝ → ℝ}
    (hf : MemLp f 2 (physicalMeasure R)) (hg : MemLp g 2 (physicalMeasure R)) :
    totalMass R (f - g) = totalMass R f - totalMass R g := by
  simpa only [totalMass, Pi.sub_apply, physicalMeasure] using
    integral_sub (hf.integrable (by norm_num)) (hg.integrable (by norm_num))

lemma totalMass_square_bound {R : ℝ} (hR : 0 < R) {f : ℝ → ℝ}
    (hf : MemLp f 2 (physicalMeasure R)) :
    (totalMass R f) ^ 2 ≤ 2 * R * (∫ t in interval R, (f t) ^ 2) := by
  have hOne : MemLp (fun _ : ℝ => (1 : ℝ)) 2 (physicalMeasure R) :=
    RhDilationRank.continuous_memLp continuous_const
  have h := RhDilationRank.moment_cauchy_sq hOne hf
  simp only [one_mul, one_pow] at h
  have hvol : (∫ t in interval R, (1 : ℝ)) = 2 * R := by
    simp [interval, integral_const, max_eq_left (by linarith : 0 ≤ R + R), two_mul]
  rw [hvol] at h
  exact h

/-- Exact finite-measure Cauchy estimate for the scalar difference. -/
theorem totalMass_difference_square_bound {R : ℝ} (hR : 0 < R) {f g : ℝ → ℝ}
    (hf : MemLp f 2 (physicalMeasure R)) (hg : MemLp g 2 (physicalMeasure R)) :
    (totalMass R f - totalMass R g) ^ 2 ≤
      2 * R * (∫ t in interval R, (f t - g t) ^ 2) := by
  have h := totalMass_square_bound hR (hf.sub hg)
  rw [totalMass_sub hf hg] at h
  simpa only [Pi.sub_apply] using h

/-- Actual physical L2 approximation forces convergence of the centering mass. -/
theorem totalMass_tendsto_of_l2_error {R : ℝ} (hR : 0 < R)
    (u : ℕ → ℝ → ℝ) (v : ℝ → ℝ)
    (hu : ∀ n, MemLp (u n) 2 (physicalMeasure R))
    (hv : MemLp v 2 (physicalMeasure R))
    (he : Tendsto (fun n => ∫ t in interval R, (u n t - v t) ^ 2) atTop (𝓝 0)) :
    Tendsto (fun n => totalMass R (u n)) atTop (𝓝 (totalMass R v)) := by
  have hs : Tendsto (fun n => (totalMass R (u n) - totalMass R v) ^ 2)
      atTop (𝓝 0) := by
    apply squeeze_zero' (g := fun n => 2 * R * (∫ t in interval R, (u n t - v t) ^ 2))
      (Eventually.of_forall (fun _ => sq_nonneg _))
    · exact Eventually.of_forall (fun n => totalMass_difference_square_bound hR (hu n) hv)
    · simpa only [mul_zero] using he.const_mul (2 * R)
  have ha := (Real.continuous_sqrt.tendsto 0).comp hs
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, Real.sqrt_zero, Real.norm_eq_abs] using ha

end RhPhysicalMassConvergence
#print axioms RhPhysicalMassConvergence.totalMass_difference_square_bound
#print axioms RhPhysicalMassConvergence.totalMass_tendsto_of_l2_error
