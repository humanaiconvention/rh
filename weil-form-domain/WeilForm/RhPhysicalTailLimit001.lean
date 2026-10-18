import RhPhysicalFiniteTail001

noncomputable section
open Set MeasureTheory Filter FourierTransform
open scoped Topology BigOperators ENNReal
namespace RhTail

lemma physical_frequency_integrable {A b : ℝ} (hb : 0 < b) {w : ℝ → ℝ}
    (hw : MemLp w 2 (RhAnchored.physicalMeasure A)) (k : ℕ) :
    Integrable (fun ξ : ℝ => multiplier (angularSquare ξ) (b+2*k)*
      spectralDensity (physicalFourierVector A w hw) ξ) volume :=
  multiplier_energy_integrable (by positivity) (complexExtension_integrable hw)
    (complexExtension_memLp hw)

lemma physical_frequency_nonneg (b : ℝ) (hb : 0 < b) (F : WholeSpace) (k : ℕ) (ξ : ℝ) :
    0 ≤ multiplier (angularSquare ξ) (b+2*k)*spectralDensity F ξ :=
  mul_nonneg (multiplier_nonneg (sq_nonneg _) (by positivity)) (sq_nonneg _)

lemma finite_frequency_physical_eq {A L : ℝ} (hA : 0 < A) (hAL : A < L)
    {v : ℝ → ℝ} (hv : MemLp v 2 (RhAnchored.physicalMeasure A))
    (C α : ℝ) (J K : ℕ) :
    finiteFrequencyEnergy (RhAnchored.beta J)
      (physicalFourierVector A (RhAnchored.primitive A v) (RhAnchored.primitive_memLp hv)) K =
      ENNReal.ofReal (RhAnchored.finiteQuadratic A C α L (J+K) v-
        RhAnchored.finiteQuadratic A C α L J v) := by
  rw [RhAnchored.finite_physical_tail hA hAL hv C α J K]
  simp only [add_sub_cancel_left, RhAnchored.beta_add]
  rw [finite_frequency_eq_sum (RhAnchored.beta_pos J), ENNReal.ofReal_sum_of_nonneg]
  · apply Finset.sum_congr rfl
    intro k hk
    exact (ofReal_integral_eq_lintegral_ofReal
      (physical_frequency_integrable (RhAnchored.beta_pos J) (RhAnchored.primitive_memLp hv) k)
      (Eventually.of_forall (physical_frequency_nonneg _ (RhAnchored.beta_pos J) _ k))).symm
  · intro k hk
    exact integral_nonneg (physical_frequency_nonneg _ (RhAnchored.beta_pos J) _ k)

lemma physical_tail_nonneg {A L : ℝ} (hA : 0 < A) (hAL : A < L)
    {v : ℝ → ℝ} (hv : MemLp v 2 (RhAnchored.physicalMeasure A))
    (C α : ℝ) (J K : ℕ) :
    0 ≤ RhAnchored.finiteQuadratic A C α L (J+K) v-
      RhAnchored.finiteQuadratic A C α L J v := by
  rw [RhAnchored.finite_physical_tail hA hAL hv C α J K]
  simp only [add_sub_cancel_left, RhAnchored.beta_add]
  exact Finset.sum_nonneg (fun k _ =>
    integral_nonneg (physical_frequency_nonneg _ (RhAnchored.beta_pos J) _ k))

theorem physical_fourier_tail_limit {A L : ℝ} (hA : 0 < A) (hAL : A < L)
    {v : ℝ → ℝ} (hv : MemLp v 2 (RhAnchored.physicalMeasure A))
    (C α : ℝ) (J : ℕ) :
    fullFrequencyEnergy (RhAnchored.beta J)
      (physicalFourierVector A (RhAnchored.primitive A v) (RhAnchored.primitive_memLp hv)) =
      ENNReal.ofReal (RhAnchored.fullQuadratic A C α L v-
        RhAnchored.finiteQuadratic A C α L J v) ∧
    0 ≤ RhAnchored.fullQuadratic A C α L v-RhAnchored.finiteQuadratic A C α L J v := by
  have hp : Tendsto (fun K : ℕ => RhAnchored.finiteQuadratic A C α L (J+K) v)
      atTop (𝓝 (RhAnchored.fullQuadratic A C α L v)) := by
    simpa only [Function.comp_def, Nat.add_comm] using
      (RhAnchored.physical_kernel_limit hA hAL hv C α).comp (tendsto_add_atTop_nat J)
  have hd := hp.sub_const (RhAnchored.finiteQuadratic A C α L J v)
  have he := (ENNReal.continuous_ofReal.tendsto
    (RhAnchored.fullQuadratic A C α L v-RhAnchored.finiteQuadratic A C α L J v)).comp hd
  have he' : Tendsto
      (finiteFrequencyEnergy (RhAnchored.beta J)
        (physicalFourierVector A (RhAnchored.primitive A v) (RhAnchored.primitive_memLp hv)))
      atTop (𝓝 (ENNReal.ofReal (RhAnchored.fullQuadratic A C α L v-
        RhAnchored.finiteQuadratic A C α L J v))) := by
    convert he using 1
    funext K
    exact finite_frequency_physical_eq hA hAL hv C α J K
  refine ⟨tendsto_nhds_unique (frequency_tail_limit (RhAnchored.beta_pos J) _) he', ?_⟩
  exact le_of_tendsto_of_tendsto tendsto_const_nhds hd
    (Eventually.of_forall (physical_tail_nonneg hA hAL hv C α J))

end RhTail
#print axioms RhTail.physical_fourier_tail_limit
