import RhFullKernelSeries001

noncomputable section
open Set MeasureTheory Filter
open scoped Topology BigOperators
namespace RhAnchored

def kernelQuadratic (A : ℝ) (K : ℝ → ℝ → ℝ) (v : ℝ → ℝ) : ℝ :=
  ∫ t in interval A, ∫ u in interval A, K t u*v u*v t
def finiteQuadratic (A C α L : ℝ) (J : ℕ) (v : ℝ → ℝ) : ℝ :=
  kernelQuadratic A (finiteKernel C α L J) v
def fullQuadratic (A C α L : ℝ) (v : ℝ → ℝ) : ℝ :=
  kernelQuadratic A (fullKernel C α L) v

lemma finiteKernel_row_tendsto {A : ℝ} (hA : 0 < A)
    {v : ℝ → ℝ} (hv : MemLp v 2 (physicalMeasure A)) (C α L B t : ℝ)
    (hB : ∀ (J : ℕ) (t u : ℝ), t ∈ interval A → u ∈ interval A →
      ‖finiteKernel C α L J t u‖ ≤ B) (ht : t ∈ interval A) :
    Tendsto (fun J : ℕ => ∫ u in interval A, finiteKernel C α L J t u*v u*v t)
      atTop (𝓝 (∫ u in interval A, fullKernel C α L t u*v u*v t)) := by
  have hv1 : IntegrableOn v (interval A) := hv.integrable (by norm_num)
  apply tendsto_integral_of_dominated_convergence (fun u => B*‖v u‖*‖v t‖)
  · intro J
    exact ((finiteKernel_row_integrable hA hv C α L J t).mul_const (v t)).aestronglyMeasurable
  · exact (hv1.norm.const_mul B).mul_const ‖v t‖
  · intro J
    apply ae_restrict_of_forall_mem measurableSet_Icc
    intro u hu
    rw [norm_mul, norm_mul]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (hB J t u ht hu) (norm_nonneg _)) (norm_nonneg _)
  · exact Eventually.of_forall (fun u =>
      ((finiteKernel_tendsto C α L t u).mul_const (v u)).mul_const (v t))

theorem physical_kernel_limit {A L : ℝ} (hA : 0 < A) (hAL : A < L)
    {v : ℝ → ℝ} (hv : MemLp v 2 (physicalMeasure A)) (C α : ℝ) :
    Tendsto (fun J : ℕ => finiteQuadratic A C α L J v) atTop
      (𝓝 (fullQuadratic A C α L v)) := by
  obtain ⟨B,hB0,hB⟩ := finiteKernel_uniform_bound (A := A) C α L
  have hv1 : IntegrableOn v (interval A) := hv.integrable (by norm_num)
  unfold finiteQuadratic fullQuadratic kernelQuadratic
  apply tendsto_integral_of_dominated_convergence
    (fun t => B*(∫ u in interval A, ‖v u‖)*‖v t‖)
  · intro J
    exact (finiteKernel_outer_integrable hA hAL hv C α J).aestronglyMeasurable
  · exact hv1.norm.const_mul _
  · intro J
    apply ae_restrict_of_forall_mem measurableSet_Icc
    intro t ht
    calc
      _ ≤ ∫ u in interval A, ‖finiteKernel C α L J t u*v u*v t‖ :=
        norm_integral_le_integral_norm _
      _ ≤ ∫ u in interval A, B*‖v u‖*‖v t‖ := by
        apply integral_mono_ae ((finiteKernel_row_integrable hA hv C α L J t).mul_const (v t)).norm
          ((hv1.norm.const_mul B).mul_const ‖v t‖)
        apply ae_restrict_of_forall_mem measurableSet_Icc
        intro u hu
        dsimp only
        rw [norm_mul, norm_mul]
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (hB J t u ht hu) (norm_nonneg _)) (norm_nonneg _)
      _ = _ := by rw [integral_mul_const, integral_const_mul]
  · apply ae_restrict_of_forall_mem measurableSet_Icc
    intro t ht
    exact finiteKernel_row_tendsto hA hv C α L B t hB ht

end RhAnchored
#print axioms RhAnchored.physical_kernel_limit
