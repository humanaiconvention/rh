import RhFullKernelIntegrability001
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.MeasureTheory.Integral.Prod

set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
open Set MeasureTheory Filter
open scoped Topology BigOperators ComplexConjugate
namespace RhEndpointComplex
open RhAnchored

theorem fullKernel_joint_continuous (C α L : ℝ) :
    Continuous (fun p : ℝ×ℝ => fullKernel C α L p.1 p.2) := by
  have h0 : Continuous (fun p : ℝ×ℝ => finiteKernel C α L 0 p.1 p.2) := by
    unfold finiteKernel anchoredKernel finitePotential
    simp only [Finset.sum_range_zero]
    fun_prop
  have hk (k : ℕ) : Continuous (fun p : ℝ×ℝ => archKernelTerm k p.1 p.2) := by
    unfold archKernelTerm anchoredKernel archTerm
    fun_prop
  exact h0.sub (continuous_tsum hk archMajorant_summable
    (fun k p => archKernelTerm_norm_le k p.1 p.2))

def complexIntegrand (C α L : ℝ) (v : ℝ→ℂ) (p : ℝ×ℝ) : ℂ :=
  (fullKernel C α L p.1 p.2 : ℂ)*conj (v p.1)*v p.2

theorem complex_integrand_integrable {A : ℝ} {v : ℝ→ℂ}
    (hv : MemLp v 2 (physicalMeasure A)) (C α L : ℝ) :
    Integrable (complexIntegrand C α L v)
      ((physicalMeasure A).prod (physicalMeasure A)) := by
  obtain ⟨B,hB0,hB⟩ := finiteKernel_uniform_bound (A := A) C α L
  have hv1 : Integrable v (physicalMeasure A) := hv.integrable (by norm_num)
  have hm : AEStronglyMeasurable (complexIntegrand C α L v)
      ((physicalMeasure A).prod (physicalMeasure A)) := by
    exact ((((Complex.continuous_ofReal.comp (fullKernel_joint_continuous C α L)).aestronglyMeasurable).mul
      (Complex.continuous_conj.comp_aestronglyMeasurable hv.aestronglyMeasurable.comp_fst)).mul hv.aestronglyMeasurable.comp_snd)
  apply ((hv1.norm.mul_prod hv1.norm).const_mul B).mono' hm
  change ∀ᵐ p ∂(volume.restrict (interval A)).prod (volume.restrict (interval A)),
    ‖complexIntegrand C α L v p‖ ≤ B*(‖v p.1‖*‖v p.2‖)
  rw [Measure.prod_restrict]
  apply ae_restrict_of_forall_mem (measurableSet_Icc.prod measurableSet_Icc)
  intro p hp
  have hb := fullKernel_bound_of_finite C α L B hB hp.1 hp.2
  calc
    _ = ‖fullKernel C α L p.1 p.2‖*‖v p.1‖*‖v p.2‖ := by
      simp only [complexIntegrand,norm_mul,Complex.norm_real,Complex.norm_conj,Real.norm_eq_abs]
    _ ≤ B*‖v p.1‖*‖v p.2‖ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hb (norm_nonneg _)) (norm_nonneg _)
    _ = _ := by ring

theorem real_integrand_integrable {A : ℝ} {v : ℝ→ℝ}
    (hv : MemLp v 2 (physicalMeasure A)) (C α L : ℝ) :
    Integrable (fun p : ℝ×ℝ => fullKernel C α L p.1 p.2*v p.2*v p.1)
      ((physicalMeasure A).prod (physicalMeasure A)) := by
  have h := (complex_integrand_integrable hv.ofReal C α L).re
  apply h.congr
  exact Eventually.of_forall (fun p => by
    simp only [RCLike.re_eq_complex_re,RCLike.ofReal_eq_complex_ofReal,complexIntegrand,Complex.mul_re,Complex.mul_im,
      Complex.conj_re,Complex.conj_im,Complex.ofReal_re,Complex.ofReal_im]
    ring)

def complexQuadratic (A C α L : ℝ) (v : ℝ→ℂ) : ℂ :=
  ∫ p : ℝ×ℝ, complexIntegrand C α L v p
    ∂((physicalMeasure A).prod (physicalMeasure A))

theorem complexQuadratic_eq_iterated {A : ℝ} {v : ℝ→ℂ}
    (hv : MemLp v 2 (physicalMeasure A)) (C α L : ℝ) :
    complexQuadratic A C α L v =
      ∫ t in interval A, ∫ u in interval A,
        (fullKernel C α L t u : ℂ)*conj (v t)*v u := by
  exact integral_prod _ (complex_integrand_integrable hv C α L)

theorem complexQuadratic_re {A : ℝ} {v : ℝ→ℂ}
    (hv : MemLp v 2 (physicalMeasure A)) (C α L : ℝ) :
    (complexQuadratic A C α L v).re =
      fullQuadratic A C α L (fun t => (v t).re)+
      fullQuadratic A C α L (fun t => (v t).im) := by
  have hi := complex_integrand_integrable hv C α L
  have hr := real_integrand_integrable hv.re C α L
  have hm := real_integrand_integrable hv.im C α L
  simp only [RCLike.re_eq_complex_re,RCLike.im_eq_complex_im] at hr hm
  unfold complexQuadratic
  have hiRe : (∫ p : ℝ×ℝ, (complexIntegrand C α L v p).re
      ∂((physicalMeasure A).prod (physicalMeasure A))) =
      (∫ p : ℝ×ℝ, complexIntegrand C α L v p
        ∂((physicalMeasure A).prod (physicalMeasure A))).re := by
    simpa only [RCLike.re_eq_complex_re] using integral_re hi
  rw [← hiRe]
  have he : (fun p : ℝ×ℝ => (complexIntegrand C α L v p).re) =
      (fun p : ℝ×ℝ => fullKernel C α L p.1 p.2*(v p.2).re*(v p.1).re+
        fullKernel C α L p.1 p.2*(v p.2).im*(v p.1).im) := by
    funext p
    simp only [complexIntegrand,Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
      Complex.conj_re,Complex.conj_im]
    ring
  rw [he,integral_add hr hm,integral_prod _ hr,integral_prod _ hm]
  rfl

theorem complex_positive_of_real {A C α L : ℝ}
    (hReal : ∀ v : ℝ→ℝ, MemLp v 2 (physicalMeasure A) → 0 ≤ fullQuadratic A C α L v)
    {v : ℝ→ℂ} (hv : MemLp v 2 (physicalMeasure A)) :
    0 ≤ (complexQuadratic A C α L v).re := by
  rw [complexQuadratic_re hv]
  exact add_nonneg (hReal _ hv.re) (hReal _ hv.im)

end RhEndpointComplex
#print axioms RhEndpointComplex.fullKernel_joint_continuous
#print axioms RhEndpointComplex.complex_integrand_integrable
#print axioms RhEndpointComplex.real_integrand_integrable
#print axioms RhEndpointComplex.complexQuadratic_eq_iterated
#print axioms RhEndpointComplex.complexQuadratic_re
#print axioms RhEndpointComplex.complex_positive_of_real
