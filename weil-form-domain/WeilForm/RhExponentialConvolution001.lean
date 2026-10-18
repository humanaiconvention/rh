import RhExponentialFourier001

noncomputable section
open Set MeasureTheory Filter FourierTransform
open scoped Topology BigOperators ENNReal Convolution
namespace RhTail

def exponentialConvolution (β : ℝ) (f : ℝ → ℂ) : ℝ → ℂ :=
  exponentialKernel β ⋆[ContinuousLinearMap.mul ℂ ℂ] f

lemma exponentialKernel_continuous (β : ℝ) : Continuous (exponentialKernel β) := by
  unfold exponentialKernel
  fun_prop

lemma exponentialKernel_norm (β t : ℝ) :
    ‖exponentialKernel β t‖=Real.exp (-β*|t|) := by
  simp only [exponentialKernel, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]

lemma exponentialKernel_norm_le_one {β : ℝ} (hβ : 0 ≤ β) (t : ℝ) :
    ‖exponentialKernel β t‖ ≤ 1 := by
  rw [exponentialKernel_norm]
  exact Real.exp_le_one_iff.mpr (by nlinarith [abs_nonneg t])

lemma exponentialConvolution_continuous {β : ℝ} (hβ : 0 ≤ β) {f : ℝ → ℂ}
    (hf : Integrable f volume) : Continuous (exponentialConvolution β f) := by
  have hB : BddAbove (range fun t : ℝ => ‖exponentialKernel β t‖) :=
    ⟨1, fun z ⟨t,ht⟩ => ht ▸ exponentialKernel_norm_le_one hβ t⟩
  exact hB.continuous_convolution_left_of_integrable
    (ContinuousLinearMap.mul ℂ ℂ) (exponentialKernel_continuous β) hf

lemma exponentialConvolution_integrable {β : ℝ} (hβ : 0 < β) {f : ℝ → ℂ}
    (hf : Integrable f volume) : Integrable (exponentialConvolution β f) volume :=
  (exponentialKernel_integrable hβ).integrable_convolution (ContinuousLinearMap.mul ℂ ℂ) hf

lemma exponentialConvolution_norm_le {β : ℝ} (hβ : 0 ≤ β) {f : ℝ → ℂ}
    (hf : Integrable f volume) (t : ℝ) :
    ‖exponentialConvolution β f t‖ ≤ ∫ u : ℝ, ‖f u‖ := by
  have hbound (u : ℝ) : ‖exponentialKernel β (t-u)*f u‖ ≤ ‖f u‖ := by
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_right (exponentialKernel_norm_le_one hβ (t-u))
      (norm_nonneg _)).trans_eq (one_mul _)
  have hi : Integrable (fun u => exponentialKernel β (t-u)*f u) volume :=
    hf.norm.mono' (((exponentialKernel_continuous β).comp
      (continuous_const.sub continuous_id)).aestronglyMeasurable.mul hf.aestronglyMeasurable)
      (Eventually.of_forall hbound)
  unfold exponentialConvolution
  rw [convolution_mul_swap]
  exact (norm_integral_le_integral_norm _).trans
    (integral_mono hi.norm hf.norm hbound)

theorem exponentialConvolution_memLp {β : ℝ} (hβ : 0 < β) {f : ℝ → ℂ}
    (hf : Integrable f volume) : MemLp (exponentialConvolution β f) 2 volume := by
  have hc := exponentialConvolution_continuous hβ.le hf
  have hi := exponentialConvolution_integrable hβ hf
  have hsq : Integrable (fun t : ℝ => ‖exponentialConvolution β f t‖^2) volume := by
    apply (hi.norm.const_mul (∫ u : ℝ, ‖f u‖)).mono'
      (hc.norm.pow 2).aestronglyMeasurable
    exact Eventually.of_forall (fun t => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      simp only [Pi.pow_apply]
      nlinarith [exponentialConvolution_norm_le hβ.le hf t,
        norm_nonneg (exponentialConvolution β f t)])
  exact (memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable).mpr hsq

theorem exponentialConvolution_fourier_ae {β : ℝ} (hβ : 0 < β) {f : ℝ → ℂ}
    (hf : Integrable f volume) (h2 : MemLp f 2 volume) :
    ∀ᵐ ξ ∂volume,
      (𝓕 ((exponentialConvolution_memLp hβ hf).toLp (exponentialConvolution β f)) : WholeSpace) ξ=
        ((2*β/(β^2+angularSquare ξ) : ℝ) : ℂ)*(𝓕 (h2.toLp f) : WholeSpace) ξ := by
  filter_upwards [integral_fourier_ae_L2 (exponentialConvolution_integrable hβ hf)
      (exponentialConvolution_memLp hβ hf), integral_fourier_ae_L2 hf h2] with ξ hg hfξ
  have he := Real.fourier_mul_convolution_eq (exponentialKernel_integrable hβ) hf ξ
  rw [exponentialKernel_fourier hβ] at he
  rw [← hg]
  exact he.trans (congrArg (fun z : ℂ => ((2*β/(β^2+angularSquare ξ) : ℝ) : ℂ)*z) hfξ)

end RhTail
#print axioms RhTail.exponentialConvolution_memLp
#print axioms RhTail.exponentialConvolution_fourier_ae
