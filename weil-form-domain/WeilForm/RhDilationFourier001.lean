import RhDilationDefs001
import RhExponentialPlancherel001
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

noncomputable section
open Set MeasureTheory Filter FourierTransform
open scoped Topology ComplexInnerProductSpace
namespace RhDilation

/-- Complex L1/L2 dilation, with exactly the real physical normalization. -/
def complexDilate (r : ℝ) (f : ℝ → ℂ) (t : ℝ) : ℂ :=
  ((Real.sqrt r)⁻¹ : ℝ) * f (t/r)

lemma complexDilate_ofReal (r : ℝ) (w : ℝ → ℝ) :
    complexDilate r (fun t => (w t : ℂ)) = fun t => (dilate r w t : ℂ) := by
  funext t
  simp only [complexDilate,dilate,Complex.ofReal_mul]

lemma complexDilate_integrable {r : ℝ} (hr : 0 < r) {f : ℝ → ℂ}
    (hf : Integrable f volume) : Integrable (complexDilate r f) volume :=
  (hf.comp_div hr.ne').const_mul _

lemma complexDilate_memLp {r : ℝ} (hr : 0 < r) {f : ℝ → ℂ}
    (hf : Integrable f volume) (h2 : MemLp f 2 volume) :
    MemLp (complexDilate r f) 2 volume := by
  apply (memLp_two_iff_integrable_sq_norm
    (complexDilate_integrable hr hf).aestronglyMeasurable).mpr
  have hi := (memLp_two_iff_integrable_sq_norm h2.aestronglyMeasurable).mp h2
  have hj := (hi.comp_div hr.ne').const_mul (((Real.sqrt r)⁻¹)^2)
  convert hj using 1
  funext t
  simp only [complexDilate,norm_mul,Complex.norm_real,Real.norm_eq_abs,mul_pow,sq_abs]

/-- Actual integral Fourier scaling. The phase and Jacobian are exact. -/
theorem fourier_complexDilate {r : ℝ} (hr : 0 < r) (f : ℝ → ℂ) (ξ : ℝ) :
    (𝓕 (complexDilate r f)) ξ = (Real.sqrt r : ℂ) * (𝓕 f) (r*ξ) := by
  rw [Real.fourier_real_eq_integral_exp_smul,Real.fourier_real_eq_integral_exp_smul]
  simp only [smul_eq_mul]
  let g : ℝ → ℂ := fun t => Complex.exp (((-2*Real.pi*t*(r*ξ):ℝ):ℂ)*Complex.I)*f t
  have he : (fun t:ℝ => Complex.exp (((-2*Real.pi*t*ξ:ℝ):ℂ)*Complex.I)*complexDilate r f t)=
      fun t => ((Real.sqrt r)⁻¹:ℝ)*g (t/r) := by
    funext t
    dsimp only [complexDilate,g]
    have hp : -2*Real.pi*(t/r)*(r*ξ) = -2*Real.pi*t*ξ := by field_simp [hr.ne']
    rw [hp]
    ring
  rw [he,integral_const_mul,Measure.integral_comp_div]
  rw [abs_of_pos hr]
  simp only [Complex.real_smul]
  have hs : (Real.sqrt r)⁻¹*r=Real.sqrt r := by
    have hsq := Real.sq_sqrt hr.le
    have hn := (Real.sqrt_pos.2 hr).ne'
    field_simp
    nlinarith
  change (((Real.sqrt r)⁻¹:ℝ):ℂ)*((r:ℂ)*(∫t:ℝ,g t))=
    (Real.sqrt r:ℂ)*(∫t:ℝ,g t)
  rw [←mul_assoc,←Complex.ofReal_mul,hs]

/-- The actual real physical dilation has the same complex Fourier formula. -/
theorem fourier_dilate_real {r : ℝ} (hr : 0 < r) (w : ℝ → ℝ) (ξ : ℝ) :
    (𝓕 (fun t => (dilate r w t : ℂ))) ξ =
      (Real.sqrt r : ℂ) * (𝓕 (fun t => (w t : ℂ))) (r*ξ) := by
  rw [←complexDilate_ofReal]
  exact fourier_complexDilate hr _ ξ

/-- L2 Fourier compatibility is only an almost-everywhere assertion. -/
theorem fourier_complexDilate_L2_ae {r : ℝ} (hr : 0 < r) {f : ℝ → ℂ}
    (hf : Integrable f volume) (h2 : MemLp f 2 volume) :
    (𝓕 ((complexDilate_memLp hr hf h2).toLp (complexDilate r f)) : RhTail.WholeSpace)
      =ᵐ[volume] fun ξ => (Real.sqrt r:ℂ)*(𝓕 f) (r*ξ) := by
  have h := RhTail.integral_fourier_ae_L2 (complexDilate_integrable hr hf)
    (complexDilate_memLp hr hf h2)
  filter_upwards [h] with ξ hξ
  rw [←hξ,fourier_complexDilate hr]

/-- Translation is converted into its exact unit complex phase. -/
theorem fourier_translate (f : ℝ → ℂ) (a ξ : ℝ) :
    (𝓕 (fun t => f (t+a))) ξ =
      Complex.exp (((2*Real.pi*a*ξ:ℝ):ℂ)*Complex.I)*(𝓕 f) ξ := by
  have h := congrFun (VectorFourier.fourierIntegral_comp_add_right
    Real.fourierChar volume (innerₗ ℝ) f a) ξ
  change (𝓕 (fun t => f (t+a))) ξ = _ at h
  rw [h]
  simp only [Circle.smul_def,smul_eq_mul,Real.fourierChar_apply,innerₗ_apply_apply,Real.inner_apply]
  congr 1
  congr 1
  push_cast
  ring

lemma translate_memLp {f : ℝ → ℂ} (h2 : MemLp f 2 volume) (a : ℝ) :
    MemLp (fun t => f (t+a)) 2 volume :=
  h2.comp_measurePreserving (measurePreserving_add_right volume a)

/-- Actual L2 translation multiplier, with AE identification retained. -/
theorem fourier_translate_L2_ae {f : ℝ → ℂ}
    (hf : Integrable f volume) (h2 : MemLp f 2 volume) (a : ℝ) :
    (𝓕 ((translate_memLp h2 a).toLp (fun t => f (t+a))) : RhTail.WholeSpace)
      =ᵐ[volume] fun ξ => Complex.exp (((2*Real.pi*a*ξ:ℝ):ℂ)*Complex.I)*
        (𝓕 (h2.toLp f) : RhTail.WholeSpace) ξ := by
  have hs := RhTail.integral_fourier_ae_L2 (hf.comp_add_right a) (translate_memLp h2 a)
  have ho := RhTail.integral_fourier_ae_L2 hf h2
  filter_upwards [hs,ho] with ξ hξ hoξ
  rw [←hξ,fourier_translate,hoξ]

end RhDilation
#print axioms RhDilation.complexDilate_memLp
#print axioms RhDilation.fourier_complexDilate
#print axioms RhDilation.fourier_dilate_real
#print axioms RhDilation.fourier_complexDilate_L2_ae
#print axioms RhDilation.fourier_translate
#print axioms RhDilation.fourier_translate_L2_ae
