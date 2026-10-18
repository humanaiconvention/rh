import RhFullKernelLimit001

noncomputable section
open Set MeasureTheory Filter
open scoped Topology BigOperators
namespace RhAnchored

lemma fullKernel_bound_of_finite {A : ℝ} (C α L B : ℝ)
    (hB : ∀ (J : ℕ) (t u : ℝ), t ∈ interval A → u ∈ interval A →
      ‖finiteKernel C α L J t u‖ ≤ B) {t u : ℝ}
    (ht : t ∈ interval A) (hu : u ∈ interval A) :
    ‖fullKernel C α L t u‖ ≤ B :=
  le_of_tendsto (finiteKernel_tendsto C α L t u).norm
    (Eventually.of_forall (fun J => hB J t u ht hu))

lemma fullKernel_row_integrable {A : ℝ} (hA : 0 < A) {v : ℝ → ℝ}
    (hv : MemLp v 2 (physicalMeasure A)) (C α L : ℝ) {t : ℝ} (ht : t ∈ interval A) :
    IntegrableOn (fun u => fullKernel C α L t u*v u) (interval A) := by
  obtain ⟨B,hB0,hB⟩ := finiteKernel_uniform_bound (A := A) C α L
  have hv1 : IntegrableOn v (interval A) := hv.integrable (by norm_num)
  have hm : AEStronglyMeasurable (fun u => fullKernel C α L t u*v u)
      (physicalMeasure A) :=
    aestronglyMeasurable_of_tendsto_ae atTop
      (fun J => (finiteKernel_row_integrable hA hv C α L J t).aestronglyMeasurable)
      (Eventually.of_forall (fun u => (finiteKernel_tendsto C α L t u).mul_const (v u)))
  apply (hv1.norm.const_mul B).mono' hm
  apply ae_restrict_of_forall_mem measurableSet_Icc
  intro u hu
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (fullKernel_bound_of_finite C α L B hB ht hu) (norm_nonneg _)

theorem fullKernel_outer_integrable {A L : ℝ} (hA : 0 < A) (hAL : A < L)
    {v : ℝ → ℝ} (hv : MemLp v 2 (physicalMeasure A)) (C α : ℝ) :
    IntegrableOn (fun t => ∫ u in interval A, fullKernel C α L t u*v u*v t) (interval A) := by
  obtain ⟨B,hB0,hB⟩ := finiteKernel_uniform_bound (A := A) C α L
  have hv1 : IntegrableOn v (interval A) := hv.integrable (by norm_num)
  have hm : AEStronglyMeasurable
      (fun t => ∫ u in interval A, fullKernel C α L t u*v u*v t) (physicalMeasure A) := by
    apply aestronglyMeasurable_of_tendsto_ae atTop
      (fun J => (finiteKernel_outer_integrable hA hAL hv C α J).aestronglyMeasurable)
    apply ae_restrict_of_forall_mem measurableSet_Icc
    intro t ht
    exact finiteKernel_row_tendsto hA hv C α L B t hB ht
  apply (hv1.norm.const_mul (B*(∫ u in interval A, ‖v u‖))).mono' hm
  apply ae_restrict_of_forall_mem measurableSet_Icc
  intro t ht
  calc
    _ ≤ ∫ u in interval A, ‖fullKernel C α L t u*v u*v t‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ u in interval A, B*‖v u‖*‖v t‖ := by
      apply integral_mono_ae ((fullKernel_row_integrable hA hv C α L ht).mul_const (v t)).norm
        ((hv1.norm.const_mul B).mul_const ‖v t‖)
      apply ae_restrict_of_forall_mem measurableSet_Icc
      intro u hu
      dsimp only
      rw [norm_mul, norm_mul]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (fullKernel_bound_of_finite C α L B hB ht hu)
          (norm_nonneg _)) (norm_nonneg _)
    _ = _ := by rw [integral_mul_const, integral_const_mul]

end RhAnchored
#print axioms RhAnchored.fullKernel_row_integrable
#print axioms RhAnchored.fullKernel_outer_integrable
