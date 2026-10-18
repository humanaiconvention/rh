import RhNativeArchKernel001
import RhWeightedCoreAttempt001

/-!
Vanishing complete archimedean energy of actual normalized smooth bump sources
concentrating at the native anchor. No global arithmetic positivity is assumed.
-/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology ENNReal
namespace RhNativeBumpCapacity
open RhAnchored RhNativeArchKernel

lemma normalized_bump_memLp (φ : ContDiffBump (0 : ℝ)) (R : ℝ) :
    MemLp (φ.normed volume) 2 (physicalMeasure R) :=
  φ.continuous_normed.memLp_of_hasCompactSupport φ.hasCompactSupport_normed

/-- Continuity and the actual anchored zero value give a quantitative small
square for each specified positive tolerance. -/
lemma kernel_small_square {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t u : ℝ, |t| ≤ δ → |u| ≤ δ →
      ‖energyKernel t u‖ ≤ ε := by
  have hc := kernel_continuous.continuousAt (x := ((0 : ℝ), (0 : ℝ)))
  rcases Metric.continuousAt_iff.mp hc ε hε with ⟨δ, hδ, hk⟩
  refine ⟨δ / 2, by positivity, ?_⟩
  intro t u ht hu
  have hd : dist (t, u) ((0 : ℝ), (0 : ℝ)) < δ := by
    simp only [Prod.dist_eq, Real.dist_eq, sub_zero]
    exact max_lt (by linarith) (by linarith)
  have hh := hk hd
  simpa only [kernel_zero_left, Real.dist_eq, sub_zero, Real.norm_eq_abs] using hh.le

/-- All of a normalized bump's mass remains attached; the restricted mass is
at most one, so no boundary or scalar companion is discarded. -/
lemma bump_quadratic_small {ε δ : ℝ} (hε : 0 ≤ ε)
    (hk : ∀ t u : ℝ, |t| ≤ δ → |u| ≤ δ → ‖energyKernel t u‖ ≤ ε)
    (φ : ContDiffBump (0 : ℝ)) (hφ : φ.rOut ≤ δ) (R : ℝ) :
    ‖kernelQuadratic R energyKernel (φ.normed volume)‖ ≤ ε := by
  let ρ : ℝ → ℝ := φ.normed volume
  have hρ : MemLp ρ 2 (physicalMeasure R) := normalized_bump_memLp φ R
  have hρ1 : Integrable ρ (physicalMeasure R) := hρ.integrable (by norm_num)
  have hnonneg (t : ℝ) : 0 ≤ ρ t := φ.nonneg_normed t
  have hi := integrand_integrable hρ
  have hp (p : ℝ × ℝ) :
      ‖energyKernel p.1 p.2 * ρ p.2 * ρ p.1‖ ≤ ε * (ρ p.1 * ρ p.2) := by
    by_cases ht : ρ p.1 = 0
    · simp only [ht, mul_zero, norm_zero, zero_mul, le_refl]
    by_cases hu : ρ p.2 = 0
    · simp only [hu, mul_zero, zero_mul, norm_zero, le_refl]
    have hst : p.1 ∈ Function.support (φ.normed volume) := ht
    have hsu : p.2 ∈ Function.support (φ.normed volume) := hu
    rw [φ.support_normed_eq, Metric.mem_ball, Real.dist_eq, sub_zero] at hst hsu
    have hb := hk p.1 p.2 (hst.le.trans hφ) (hsu.le.trans hφ)
    have hn1 : ‖ρ p.1‖ = ρ p.1 := by
      rw [Real.norm_eq_abs, abs_of_nonneg (hnonneg p.1)]
    have hn2 : ‖ρ p.2‖ = ρ p.2 := by
      rw [Real.norm_eq_abs, abs_of_nonneg (hnonneg p.2)]
    rw [norm_mul, norm_mul, hn1, hn2]
    nlinarith [mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hb (hnonneg p.2)) (hnonneg p.1)]
  have hmass0 : 0 ≤ ∫ t in interval R, ρ t := integral_nonneg hnonneg
  have hmass1 : (∫ t in interval R, ρ t) ≤ 1 := by
    have h := setIntegral_le_integral (φ.integrable_normed (μ := volume))
      (Eventually.of_forall hnonneg) (s := interval R)
    simpa only [φ.integral_normed] using h
  have he : kernelQuadratic R energyKernel ρ =
      ∫ p : ℝ × ℝ, energyKernel p.1 p.2 * ρ p.2 * ρ p.1
        ∂((physicalMeasure R).prod (physicalMeasure R)) := (integral_prod _ hi).symm
  rw [he]
  calc
    _ ≤ ∫ p : ℝ × ℝ, ‖energyKernel p.1 p.2 * ρ p.2 * ρ p.1‖
        ∂((physicalMeasure R).prod (physicalMeasure R)) := norm_integral_le_integral_norm _
    _ ≤ ∫ p : ℝ × ℝ, ε * (ρ p.1 * ρ p.2)
        ∂((physicalMeasure R).prod (physicalMeasure R)) :=
      integral_mono hi.norm ((hρ1.mul_prod hρ1).const_mul ε) hp
    _ = ε * (∫ t in interval R, ρ t) ^ 2 := by
      rw [integral_const_mul]
      have hprod := integral_prod_mul (μ := physicalMeasure R) (ν := physicalMeasure R) ρ ρ
      rw [hprod]
      simp only [physicalMeasure, pow_two]
    _ ≤ ε := by
      have hs : (∫ t in interval R, ρ t) ^ 2 ≤ 1 := by
        nlinarith
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hs hε

/-- The normalized bumps themselves have vanishing native complete tail energy.
This is an actual capacity calculation, not an assumed approximation premise. -/
theorem normalized_bump_quadratic_tendsto_zero
    (φ : ℕ → ContDiffBump (0 : ℝ))
    (hφ : Tendsto (fun n => (φ n).rOut) atTop (𝓝 0)) (R : ℝ) :
    Tendsto (fun n => kernelQuadratic R energyKernel ((φ n).normed volume))
      atTop (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  rcases kernel_small_square (half_pos hε) with ⟨δ, hδ, hk⟩
  have he : ∀ᶠ n in atTop, (φ n).rOut < δ :=
    (tendsto_order.mp hφ).2 δ hδ
  filter_upwards [he] with n hn
  have hb := bump_quadratic_small (half_pos hε).le hk (φ n) hn.le R
  rw [Real.dist_eq, sub_zero, ← Real.norm_eq_abs]
  exact lt_of_le_of_lt hb (by linarith)

/-- ENNReal complete-energy convergence follows from the exact native dictionary. -/
theorem normalized_bump_full_energy_tendsto_zero
    (φ : ℕ → ContDiffBump (0 : ℝ))
    (hφ : Tendsto (fun n => (φ n).rOut) atTop (𝓝 0))
    {R : ℝ} (hR : 0 < R) :
    Tendsto (fun n => RhTail.fullFrequencyEnergy (1 / 2)
      (RhTail.physicalFourierVector R (primitive R ((φ n).normed volume))
        (primitive_memLp (normalized_bump_memLp (φ n) R)))) atTop (𝓝 0) := by
  have h := (ENNReal.continuous_ofReal.tendsto 0).comp
    (normalized_bump_quadratic_tendsto_zero φ hφ R)
  have he : (fun n => RhTail.fullFrequencyEnergy (1 / 2)
      (RhTail.physicalFourierVector R (primitive R ((φ n).normed volume))
        (primitive_memLp (normalized_bump_memLp (φ n) R)))) =
      (fun n => ENNReal.ofReal (kernelQuadratic R energyKernel ((φ n).normed volume))) := by
    funext n
    exact full_energy_identity hR (normalized_bump_memLp (φ n) R)
  rw [he]
  simpa only [Function.comp_def, ENNReal.ofReal_zero] using h

end RhNativeBumpCapacity
#print axioms RhNativeBumpCapacity.kernel_small_square
#print axioms RhNativeBumpCapacity.bump_quadratic_small
#print axioms RhNativeBumpCapacity.normalized_bump_quadratic_tendsto_zero
#print axioms RhNativeBumpCapacity.normalized_bump_full_energy_tendsto_zero
