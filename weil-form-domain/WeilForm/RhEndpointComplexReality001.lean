import RhFullKernelLimit001

noncomputable section
open Set MeasureTheory Filter
namespace RhEndpointComplex
open RhAnchored
lemma anchoredKernel_symmetric_of_even (f : ℝ→ℝ) (hf : ∀x,f (-x)=f x) (t u : ℝ) :
    anchoredKernel f t u = anchoredKernel f u t := by
  have hdiff : f (t-u)=f (u-t) := by
    rw [show t-u=-(u-t) by ring,hf]
  unfold anchoredKernel
  rw [hf u,hf t,hdiff]
  ring

theorem fullKernel_symmetric (C α L t u : ℝ) :
    fullKernel C α L t u = fullKernel C α L u t := by
  have hf : finiteKernel C α L 0 t u = finiteKernel C α L 0 u t := by
    apply anchoredKernel_symmetric_of_even
    intro x
    simp [finitePotential,neg_div,Real.cosh_neg,abs_neg]
  unfold fullKernel
  rw [hf]
  congr 1
  apply tsum_congr
  intro k
  apply anchoredKernel_symmetric_of_even
  intro x
  simp [archTerm,abs_neg]


end RhEndpointComplex
#print axioms RhEndpointComplex.fullKernel_symmetric
