import RhFourierMonotone001
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

noncomputable section
open Set MeasureTheory Filter FourierTransform SchwartzMap
open scoped Topology BigOperators ENNReal SchwartzMap
namespace RhTail

lemma integral_fourier_continuous {f : ℝ → ℂ} (hf : Integrable f volume) :
    Continuous (𝓕 f) :=
  VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
    (innerSL ℝ).continuous₂ hf

theorem integral_fourier_ae_L2 {f : ℝ → ℂ}
    (hf : Integrable f volume) (h2 : MemLp f 2 volume) :
    (𝓕 f) =ᵐ[volume] (𝓕 (h2.toLp f) : WholeSpace) := by
  let F : WholeSpace := h2.toLp f
  apply ae_eq_of_integral_contDiff_smul_eq
    (integral_fourier_continuous hf).locallyIntegrable
    ((Lp.memLp (𝓕 F)).locallyIntegrable (by norm_num))
  intro g hg hc
  have hcC : HasCompactSupport (Complex.ofRealCLM ∘ g) := hc.comp_left rfl
  have hgC := Complex.ofRealCLM.contDiff.comp hg
  let G : 𝓢(ℝ,ℂ) := hcC.toSchwartzMap hgC
  have hG (x : ℝ) : G x=(g x : ℂ) := rfl
  have hdist := congrArg (fun D : 𝓢'(ℝ,ℂ) => D G)
    (Lp.fourier_toTemperedDistribution_eq F)
  have hd : (∫ x : ℝ, (𝓕 G) x*F x)=∫ x : ℝ, G x*(𝓕 F) x := by
    simpa only [TemperedDistribution.fourier_apply, Lp.toTemperedDistribution_apply,
      smul_eq_mul] using hdist
  have hfub : (∫ x : ℝ, (𝓕 f) x*G x)=∫ x : ℝ, f x*(𝓕 G) x := by
    simpa using! VectorFourier.integral_bilin_fourierIntegral_eq_flip
      (ContinuousLinearMap.mul ℂ ℂ) (L := innerₗ ℝ)
      Real.continuous_fourierChar continuous_inner hf G.integrable
  calc
    _ = ∫ x : ℝ, (𝓕 f) x*G x := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun x => by
        dsimp only
        rw [hG]
        simp only [Complex.real_smul]
        ring)
    _ = ∫ x : ℝ, f x*(𝓕 G) x := hfub
    _ = ∫ x : ℝ, (𝓕 G) x*F x := by
      apply integral_congr_ae
      filter_upwards [h2.coeFn_toLp] with x hx
      change f x*(𝓕 G) x=(𝓕 G) x*(h2.toLp f) x
      rw [hx]
      ring
    _ = ∫ x : ℝ, G x*(𝓕 F) x := hd
    _ = _ := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun x => by
        dsimp only
        rw [hG]
        simp only [Complex.real_smul])

end RhTail
#print axioms RhTail.integral_fourier_ae_L2
