import RhSupportInclusion001
import RhFinitePrimitiveEndpoint001
import Mathlib.MeasureTheory.Integral.Prod

noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace RhSupportLocalization
open RhAnchored
theorem kernel_joint_integrable {A : ℝ} (K : ℝ→ℝ→ℝ)
    (hK : Continuous (fun p : ℝ×ℝ => K p.1 p.2)) {f g : ℝ→ℝ}
    (hf : MemLp f 2 (physicalMeasure A)) (hg : MemLp g 2 (physicalMeasure A)) :
    Integrable (fun p : ℝ×ℝ => K p.1 p.2*f p.2*g p.1)
      ((physicalMeasure A).prod (physicalMeasure A)) := by
  have hc : IsCompact ((interval A) ×ˢ (interval A)) := isCompact_Icc.prod isCompact_Icc
  obtain ⟨B,hB⟩ := hc.bddAbove_image hK.norm.continuousOn
  have hbound (t u : ℝ) (ht : t∈interval A) (hu : u∈interval A) : ‖K t u‖≤max B 0 :=
    (hB (mem_image_of_mem _ (show (t,u)∈(interval A) ×ˢ (interval A) from ⟨ht,hu⟩))).trans
      (le_max_left _ _)
  have hf1 : Integrable f (physicalMeasure A) := hf.integrable (by norm_num)
  have hg1 : Integrable g (physicalMeasure A) := hg.integrable (by norm_num)
  have hm : AEStronglyMeasurable (fun p : ℝ×ℝ => K p.1 p.2*f p.2*g p.1)
      ((physicalMeasure A).prod (physicalMeasure A)) :=
    (hK.aestronglyMeasurable.mul hf.aestronglyMeasurable.comp_snd).mul
      hg.aestronglyMeasurable.comp_fst
  apply ((hg1.norm.mul_prod hf1.norm).const_mul (max B 0)).mono' hm
  change ∀ᵐ p ∂(volume.restrict (interval A)).prod (volume.restrict (interval A)),
    ‖K p.1 p.2*f p.2*g p.1‖≤max B 0*(‖g p.1‖*‖f p.2‖)
  rw [Measure.prod_restrict]
  apply ae_restrict_of_forall_mem (measurableSet_Icc.prod measurableSet_Icc)
  intro p hp
  rw [norm_mul,norm_mul]
  have h := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (hbound p.1 p.2 hp.1 hp.2) (norm_nonneg (f p.2))) (norm_nonneg (g p.1))
  nlinarith


end RhSupportLocalization
#print axioms RhSupportLocalization.kernel_joint_integrable
