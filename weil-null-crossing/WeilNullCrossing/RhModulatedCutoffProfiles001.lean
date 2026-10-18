import RhSmoothKernelGraphBound001
import Mathlib.Analysis.Normed.Group.Bounded

/-! PRIVATE actual modulated cutoff profiles. Uniform derivative bounds are
proved for the literal smooth/compact data, then used only for complete-domain
membership/capacity. No arithmetic sign or positivity payment is asserted.
-/
set_option maxHeartbeats 150000
noncomputable section
open Set MeasureTheory Filter
open scoped Topology ContDiff
namespace RhModulatedCutoffProfiles
open RhAnchored RhWeightedMeasureEmbedding RhSmoothJetLifts
open RhTranslatedJetCapacity RhSmoothKernelGraphBound

 def profile (f : ℝ → ℝ) (chi : ContDiffBump (0 : ℝ)) (x : ℝ) (n : ℕ) (u : ℝ) : ℝ :=
  f (x + u / scale n) * chi u

lemma profile_contDiff (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f)
    (chi : ContDiffBump (0 : ℝ)) (x : ℝ) (n : ℕ) :
    ContDiff ℝ ∞ (profile f chi x n) :=
  (hf.comp (contDiff_const.add (contDiff_id.div_const _))).mul chi.contDiff

lemma profile_tsupport (f : ℝ → ℝ) (chi : ContDiffBump (0 : ℝ)) (x : ℝ) (n : ℕ) :
    tsupport (profile f chi x n) ⊆ Ioo (-radius chi) (radius chi) := by
  intro u hu
  have hchi : u ∈ tsupport (chi : ℝ → ℝ) := tsupport_mul_subset_right hu
  rw [chi.tsupport_eq, Metric.mem_closedBall, Real.dist_eq, sub_zero] at hchi
  have hb := abs_le.mp hchi
  constructor <;> unfold radius <;> linarith

lemma profile_deriv (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f)
    (chi : ContDiffBump (0 : ℝ)) (x : ℝ) (n : ℕ) (u : ℝ) :
    deriv (profile f chi x n) u =
      (deriv f (x + u / scale n) / scale n) * chi u +
        f (x + u / scale n) * deriv (chi : ℝ → ℝ) u := by
  have hlin : DifferentiableAt ℝ (fun y : ℝ => x + y / scale n) u := by fun_prop
  have hfd : DifferentiableAt ℝ f (x + u / scale n) := hf.differentiable (by simp) _
  have hchi : ContDiff ℝ ∞ (chi : ℝ → ℝ) := chi.contDiff
  have hcd : DifferentiableAt ℝ (chi : ℝ → ℝ) u := hchi.differentiable (by simp) _
  change deriv ((f ∘ (fun y : ℝ => x + y / scale n)) * (chi : ℝ → ℝ)) u = _
  rw [deriv_mul (hfd.comp u hlin) hcd, deriv_comp u hfd hlin]
  simp only [Function.comp_def, deriv_const_add, deriv_div_const, deriv_id'', one_div,
    div_eq_mul_inv]
  rw [deriv_mul_const differentiableAt_id, deriv_id'', one_mul]

/-- Actual global bounds exist because the fixed smooth function, its
first derivative, the bump and its first derivative have compact support. -/
theorem exists_uniform_derivative_bound (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (chi : ContDiffBump (0 : ℝ)) (x : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ n : ℕ,
      (∫ u in interval (radius chi), (deriv (profile f chi x n) u)^2) ≤ M := by
  obtain ⟨A0, hA0⟩ := hc.exists_bound_of_continuous hf.continuous
  obtain ⟨A1, hA1⟩ := hc.deriv.exists_bound_of_continuous (hf.continuous_deriv (by simp))
  obtain ⟨B0, hB0⟩ := chi.hasCompactSupport.exists_bound_of_continuous chi.continuous
  obtain ⟨B1, hB1⟩ := chi.hasCompactSupport.deriv.exists_bound_of_continuous
    ((chi.contDiff : ContDiff ℝ ∞ (chi : ℝ → ℝ)).continuous_deriv (by simp))
  have hA00 : 0 ≤ A0 := (norm_nonneg (f 0)).trans (hA0 0)
  have hA10 : 0 ≤ A1 := (norm_nonneg (deriv f 0)).trans (hA1 0)
  have hB00 : 0 ≤ B0 := (norm_nonneg (chi 0)).trans (hB0 0)
  have hB10 : 0 ≤ B1 := (norm_nonneg (deriv (chi : ℝ → ℝ) 0)).trans (hB1 0)
  let K := A1*B0+A0*B1
  have hK : 0 ≤ K := add_nonneg (mul_nonneg hA10 hB00) (mul_nonneg hA00 hB10)
  have hR := radius_pos chi
  refine ⟨2 * radius chi * K^2, by positivity, ?_⟩
  intro n
  have hpoint (u : ℝ) : ‖deriv (profile f chi x n) u‖ ≤ K := by
    have hi : ‖(scale n)⁻¹‖ ≤ 1 := by
      rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (scale_pos n))]
      exact (inv_le_one₀ (scale_pos n)).mpr (scale_ge_one n)
    have ha : ‖deriv f (x + u / scale n) / scale n‖ ≤ A1 := by
      rw [div_eq_mul_inv, norm_mul]
      exact (mul_le_mul (hA1 _) hi (norm_nonneg _) hA10).trans_eq (mul_one A1)
    rw [profile_deriv f hf chi x n u]
    calc
      _ ≤ ‖deriv f (x + u / scale n) / scale n * chi u‖ +
          ‖f (x + u / scale n) * deriv (chi : ℝ → ℝ) u‖ := norm_add_le _ _
      _ = ‖deriv f (x + u / scale n) / scale n‖ * ‖chi u‖ +
          ‖f (x + u / scale n)‖ * ‖deriv (chi : ℝ → ℝ) u‖ := by rw [norm_mul, norm_mul]
      _ ≤ A1*B0+A0*B1 := add_le_add
        (mul_le_mul ha (hB0 u) (norm_nonneg _) hA10)
        (mul_le_mul (hA0 _) (hB1 u) (norm_nonneg _) hA00)
  have hsquare (u : ℝ) : (deriv (profile f chi x n) u)^2 ≤ K^2 := by
    simpa only [Real.norm_eq_abs, sq_abs] using
      (sq_le_sq₀ (norm_nonneg _) hK).mpr (hpoint u)
  have hd := RhSmoothDerivativeDictionary.derivative_memLp (R := radius chi)
    (profile_contDiff f hf chi x n)
  have hi := integral_mono (RhTail.physical_square_integrable hd)
    (integrable_const (K^2) : Integrable (fun _ : ℝ => K^2) (physicalMeasure (radius chi))) hsquare
  have hv : (∫ u in interval (radius chi), K^2) = (2 * radius chi) * K^2 := by
    simp [interval, integral_const, Real.volume_Icc,
      Real.toNNReal_of_nonneg (by linarith : 0 ≤ radius chi - -radius chi),
      max_eq_left (by linarith : 0 ≤ radius chi + radius chi), two_mul]
  exact hi.trans_eq hv

/-- Actual complete-domain vector whose physical representative is the
literal product f(t)*chi((n+1)*(t-x)); proved below AE, not pointwise on L2. -/
def cutoffVector (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f)
    (chi : ContDiffBump (0 : ℝ)) (x : ℝ) (n : ℕ) : WeightedSpace :=
  jetVector 0 (smoothLift (radius_pos chi) (profile f chi x n) (profile_contDiff f hf chi x n))
    (smoothLift_supported (radius_pos chi) (profile f chi x n) (profile_contDiff f hf chi x n)) x n

/-- UNCONDITIONAL for the prescribed smooth compact f and genuine bump.
Uniform profile derivative control is proved above, not supplied as a premise. -/
theorem cutoffVector_norm_tendsto (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (chi : ContDiffBump (0 : ℝ)) (x : ℝ) :
    Tendsto (fun n => ‖cutoffVector f hf chi x n‖) atTop (𝓝 0) := by
  obtain ⟨M, hM, hD⟩ := exists_uniform_derivative_bound f hf hc chi x
  exact variable_smooth_capacity (radius_pos chi) (profile f chi x)
    (profile_contDiff f hf chi x) x hD

/-- Exact literal cutoff-product identification only almost everywhere. -/
theorem cutoffVector_physical_ae (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f)
    (chi : ContDiffBump (0 : ℝ)) (x : ℝ) (n : ℕ) :
    physicalEmbedding (cutoffVector f hf chi x n) =ᵐ[volume]
      fun t => (f t * chi ((t-x)*scale n) : ℂ) := by
  have h := variable_smooth_physical_ae (radius_pos chi) (profile f chi x)
    (profile_contDiff f hf chi x) (profile_tsupport f chi x) x n
  filter_upwards [h] with t ht
  calc
    _ = (profile f chi x n ((t-x)*scale n) : ℂ) := ht
    _ = _ := by exact_mod_cast modulated_profile_identity f (chi : ℝ → ℝ) x t n

end RhModulatedCutoffProfiles
#print axioms RhModulatedCutoffProfiles.profile_deriv
#print axioms RhModulatedCutoffProfiles.exists_uniform_derivative_bound
#print axioms RhModulatedCutoffProfiles.cutoffVector_norm_tendsto
#print axioms RhModulatedCutoffProfiles.cutoffVector_physical_ae
