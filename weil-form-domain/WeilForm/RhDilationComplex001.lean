import RhSupportLocalization001
import RhAllPrimeUnclosedTarget001

set_option maxHeartbeats 0
noncomputable section
open Set MeasureTheory Filter
open scoped Topology BigOperators ComplexConjugate
namespace RhDilationComplex
open RhAnchored RhSupport

def complexIntegrand (K:ℝ→ℝ→ℝ) (v:ℝ→ℂ) (p:ℝ×ℝ):ℂ :=
  (K p.1 p.2:ℂ)*conj (v p.1)*v p.2

/-- Compact-kernel integrability for the actual complex L2 representative. -/
theorem complex_joint_integrable {R:ℝ} {K:ℝ→ℝ→ℝ}
    (hK:Continuous (fun p:ℝ×ℝ=>K p.1 p.2)) {v:ℝ→ℂ}
    (hv:MemLp v 2 (physicalMeasure R)) :
    Integrable (complexIntegrand K v) ((physicalMeasure R).prod (physicalMeasure R)) := by
  have hc:IsCompact ((interval R) ×ˢ (interval R)):=isCompact_Icc.prod isCompact_Icc
  obtain ⟨B,hB⟩:=hc.bddAbove_image hK.norm.continuousOn
  have hbound (t u:ℝ) (ht:t∈interval R) (hu:u∈interval R):‖K t u‖≤max B 0 :=
    (hB (mem_image_of_mem _ (show (t,u)∈(interval R) ×ˢ (interval R) from ⟨ht,hu⟩))).trans
      (le_max_left _ _)
  have hv1:Integrable v (physicalMeasure R):=hv.integrable (by norm_num)
  have hm:AEStronglyMeasurable (complexIntegrand K v)
      ((physicalMeasure R).prod (physicalMeasure R)) :=
    (((Complex.continuous_ofReal.comp hK).aestronglyMeasurable.mul
      (Complex.continuous_conj.comp_aestronglyMeasurable hv.aestronglyMeasurable.comp_fst)).mul
      hv.aestronglyMeasurable.comp_snd)
  apply ((hv1.norm.mul_prod hv1.norm).const_mul (max B 0)).mono' hm
  change ∀ᵐp ∂(volume.restrict (interval R)).prod (volume.restrict (interval R)),
    ‖complexIntegrand K v p‖≤max B 0*(‖v p.1‖*‖v p.2‖)
  rw [Measure.prod_restrict]
  apply ae_restrict_of_forall_mem (measurableSet_Icc.prod measurableSet_Icc)
  intro p hp
  calc
    _=‖K p.1 p.2‖*‖v p.1‖*‖v p.2‖ := by
      simp only [complexIntegrand,norm_mul,Complex.norm_real,Complex.norm_conj,Real.norm_eq_abs]
    _≤max B 0*‖v p.1‖*‖v p.2‖ :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (hbound p.1 p.2 hp.1 hp.2) (norm_nonneg _)) (norm_nonneg _)
    _=_ := by ring

lemma complex_energy_eq_product {R:ℝ} {K:ℝ→ℝ→ℝ}
    (hK:Continuous (fun p:ℝ×ℝ=>K p.1 p.2)) {v:ℝ→ℂ}
    (hv:MemLp v 2 (physicalMeasure R)) :
    complexEnergy R K v=∫p:ℝ×ℝ,complexIntegrand K v p
      ∂((physicalMeasure R).prod (physicalMeasure R)) :=
  (integral_prod _ (complex_joint_integrable hK hv)).symm

/-- Real and imaginary physical L2 components split the actual energy. -/
theorem complex_energy_re {R:ℝ} {K:ℝ→ℝ→ℝ}
    (hK:Continuous (fun p:ℝ×ℝ=>K p.1 p.2)) {v:ℝ→ℂ}
    (hv:MemLp v 2 (physicalMeasure R)) :
    (complexEnergy R K v).re=
      kernelQuadratic R K (fun t=>(v t).re)+kernelQuadratic R K (fun t=>(v t).im) := by
  have hi:=complex_joint_integrable hK hv
  have hr:=RhSupportLocalization.kernel_joint_integrable K hK hv.re hv.re
  have hm:=RhSupportLocalization.kernel_joint_integrable K hK hv.im hv.im
  simp only [RCLike.re_eq_complex_re,RCLike.im_eq_complex_im] at hr hm
  rw [complex_energy_eq_product hK hv]
  have hiRe : (∫p:ℝ×ℝ,(complexIntegrand K v p).re
      ∂((physicalMeasure R).prod (physicalMeasure R)))=
      (∫p:ℝ×ℝ,complexIntegrand K v p
      ∂((physicalMeasure R).prod (physicalMeasure R))).re := by
    simpa only [RCLike.re_eq_complex_re] using integral_re hi
  rw [←hiRe]
  have he : (fun p:ℝ×ℝ=>(complexIntegrand K v p).re)=
      fun p=>K p.1 p.2*(v p.2).re*(v p.1).re+K p.1 p.2*(v p.2).im*(v p.1).im := by
    funext p
    simp only [complexIntegrand,Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
      Complex.conj_re,Complex.conj_im]
    ring
  rw [he,integral_add hr hm,integral_prod _ hr,integral_prod _ hm]
  rfl

lemma complex_energy_conj {R:ℝ} {K:ℝ→ℝ→ℝ}
    (hK:Continuous (fun p:ℝ×ℝ=>K p.1 p.2)) (hSym:∀t u,K t u=K u t)
    {v:ℝ→ℂ} (hv:MemLp v 2 (physicalMeasure R)) :
    conj (complexEnergy R K v)=complexEnergy R K v := by
  rw [complex_energy_eq_product hK hv,←integral_conj]
  calc
    _=∫p:ℝ×ℝ,complexIntegrand K v p.swap
      ∂((physicalMeasure R).prod (physicalMeasure R)) := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun p=>by
        dsimp only [complexIntegrand,Prod.fst_swap,Prod.snd_swap]
        rw [hSym p.2 p.1]
        apply Complex.ext
        · simp only [Complex.conj_re,Complex.conj_im,Complex.mul_re,Complex.mul_im,
            Complex.ofReal_re,Complex.ofReal_im]
          ring
        · simp only [Complex.conj_re,Complex.conj_im,Complex.mul_re,Complex.mul_im,
            Complex.ofReal_re,Complex.ofReal_im]
          ring)
    _=_ := integral_prod_swap (complexIntegrand K v)

theorem complex_energy_im {R:ℝ} {K:ℝ→ℝ→ℝ}
    (hK:Continuous (fun p:ℝ×ℝ=>K p.1 p.2)) (hSym:∀t u,K t u=K u t)
    {v:ℝ→ℂ} (hv:MemLp v 2 (physicalMeasure R)) : (complexEnergy R K v).im=0 := by
  have h:=congrArg Complex.im (complex_energy_conj hK hSym hv)
  simp only [Complex.conj_im] at h
  linarith

/-- Positivity is transferred only after an actual all-real-input bound. -/
theorem complex_positive_of_real {R:ℝ} {K:ℝ→ℝ→ℝ}
    (hK:Continuous (fun p:ℝ×ℝ=>K p.1 p.2)) (hSym:∀t u,K t u=K u t)
    (hReal:∀f:ℝ→ℝ,MemLp f 2 (physicalMeasure R)→0≤kernelQuadratic R K f)
    {v:ℝ→ℂ} (hv:MemLp v 2 (physicalMeasure R)) :
    0≤(complexEnergy R K v).re ∧ (complexEnergy R K v).im=0 := by
  constructor
  · rw [complex_energy_re hK hv]
    exact add_nonneg (hReal _ hv.re) (hReal _ hv.im)
  · exact complex_energy_im hK hSym hv

end RhDilationComplex
#print axioms RhDilationComplex.complex_joint_integrable
#print axioms RhDilationComplex.complex_energy_eq_product
#print axioms RhDilationComplex.complex_energy_re
#print axioms RhDilationComplex.complex_energy_im
#print axioms RhDilationComplex.complex_positive_of_real
