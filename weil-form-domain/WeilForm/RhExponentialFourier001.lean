import RhFourierCompatibility001
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Fourier.Convolution

noncomputable section
open Set MeasureTheory Filter FourierTransform
open scoped Topology BigOperators ENNReal Convolution
namespace RhTail

def exponentialKernel (β : ℝ) (t : ℝ) : ℂ := (Real.exp (-β*|t|) : ℂ)
def angularFrequency (ξ : ℝ) : ℝ := 2*Real.pi*ξ
def leftLaplace (β ξ : ℝ) : ℂ := (β : ℂ)-(angularFrequency ξ : ℂ)*Complex.I
def rightLaplace (β ξ : ℝ) : ℂ := -(β : ℂ)-(angularFrequency ξ : ℂ)*Complex.I
def exponentialFourierIntegrand (β ξ t : ℝ) : ℂ :=
  Complex.exp ((-2*Real.pi*t*ξ : ℝ)*Complex.I)*exponentialKernel β t

lemma exponential_integrand_left (β ξ : ℝ) {t : ℝ} (ht : t ≤ 0) :
    exponentialFourierIntegrand β ξ t=Complex.exp (leftLaplace β ξ*t) := by
  unfold exponentialFourierIntegrand exponentialKernel leftLaplace angularFrequency
  rw [abs_of_nonpos ht, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma exponential_integrand_right (β ξ : ℝ) {t : ℝ} (ht : 0 < t) :
    exponentialFourierIntegrand β ξ t=Complex.exp (rightLaplace β ξ*t) := by
  unfold exponentialFourierIntegrand exponentialKernel rightLaplace angularFrequency
  rw [abs_of_pos ht, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma leftLaplace_re (β ξ : ℝ) : (leftLaplace β ξ).re=β := by
  simp [leftLaplace]
lemma rightLaplace_re (β ξ : ℝ) : (rightLaplace β ξ).re= -β := by
  simp [rightLaplace]

lemma exponential_integrand_integrable {β : ℝ} (hβ : 0 < β) (ξ : ℝ) :
    Integrable (exponentialFourierIntegrand β ξ) volume := by
  have hl := integrableOn_exp_mul_complex_Iic
    (a := leftLaplace β ξ) (by simpa only [leftLaplace_re] using hβ) 0
  have hr := integrableOn_exp_mul_complex_Ioi
    (a := rightLaplace β ξ) (by simpa only [rightLaplace_re] using neg_neg_of_pos hβ) 0
  have hl' : IntegrableOn (exponentialFourierIntegrand β ξ) (Iic 0) := by
    apply hl.congr
    exact ae_restrict_of_forall_mem measurableSet_Iic
      (fun t ht => (exponential_integrand_left β ξ ht).symm)
  have hr' : IntegrableOn (exponentialFourierIntegrand β ξ) (Ioi 0) := by
    apply hr.congr
    exact ae_restrict_of_forall_mem measurableSet_Ioi
      (fun t ht => (exponential_integrand_right β ξ ht).symm)
  simpa only [Iic_union_Ioi, integrableOn_univ] using hl'.union hr'

theorem exponentialKernel_integrable {β : ℝ} (hβ : 0 < β) :
    Integrable (exponentialKernel β) volume := by
  have he : exponentialFourierIntegrand β 0=exponentialKernel β := by
    funext t
    simp [exponentialFourierIntegrand]
  rw [← he]
  exact exponential_integrand_integrable hβ 0

theorem exponentialKernel_fourier_laplace {β : ℝ} (hβ : 0 < β) (ξ : ℝ) :
    (𝓕 (exponentialKernel β)) ξ=(leftLaplace β ξ)⁻¹-(rightLaplace β ξ)⁻¹ := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  simp only [smul_eq_mul]
  change (∫ t : ℝ, exponentialFourierIntegrand β ξ t)=_
  rw [← integral_add_compl measurableSet_Iic (exponential_integrand_integrable hβ ξ), compl_Iic]
  have hl : (∫ t : ℝ in Iic 0, exponentialFourierIntegrand β ξ t)=
      ∫ t : ℝ in Iic 0, Complex.exp (leftLaplace β ξ*t) := by
    apply setIntegral_congr_fun measurableSet_Iic
    intro t ht
    exact exponential_integrand_left β ξ ht
  have hr : (∫ t : ℝ in Ioi 0, exponentialFourierIntegrand β ξ t)=
      ∫ t : ℝ in Ioi 0, Complex.exp (rightLaplace β ξ*t) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    exact exponential_integrand_right β ξ ht
  rw [hl, hr, integral_exp_mul_complex_Iic
    (by simpa only [leftLaplace_re] using hβ), integral_exp_mul_complex_Ioi
    (by simpa only [rightLaplace_re] using neg_neg_of_pos hβ)]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_div, neg_div]
  ring

theorem exponentialKernel_fourier {β : ℝ} (hβ : 0 < β) (ξ : ℝ) :
    (𝓕 (exponentialKernel β)) ξ=
      ((2*β/(β^2+angularSquare ξ) : ℝ) : ℂ) := by
  rw [exponentialKernel_fourier_laplace hβ]
  have hL : leftLaplace β ξ ≠ 0 := by
    intro h
    have hr := congrArg Complex.re h
    rw [leftLaplace_re] at hr
    simp only [Complex.zero_re] at hr
    linarith
  have hR : rightLaplace β ξ ≠ 0 := by
    intro h
    have hr := congrArg Complex.re h
    rw [rightLaplace_re] at hr
    simp only [Complex.zero_re] at hr
    linarith
  have hden : β^2+angularSquare ξ ≠ 0 := ne_of_gt (by
    unfold angularSquare
    positivity)
  have hdenC : ((β^2+angularSquare ξ : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hden
  rw [Complex.ofReal_div]
  field_simp [hL, hR, hdenC]
  unfold leftLaplace rightLaplace angularFrequency angularSquare
  push_cast
  ring_nf <;> norm_num [Complex.I_sq]

end RhTail
#print axioms RhTail.exponentialKernel_integrable
#print axioms RhTail.exponentialKernel_fourier
