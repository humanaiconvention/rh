import RhFinitePrimitiveIdentity001

/-! Integrability certificates for both sides of the finite-J identity. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology Interval BigOperators
namespace RhAnchored

lemma finiteKernel_row_integrable {A : ℝ} (hA : 0 < A) {v : ℝ → ℝ}
    (hv : MemLp v 2 (physicalMeasure A)) (C α L : ℝ) (J : ℕ) (t : ℝ) :
    IntegrableOn (fun u => finiteKernel C α L J t u * v u) (interval A) := by
  have hv1 : IntegrableOn v (interval A) := hv.integrable (by norm_num)
  have hc : ContinuousOn (finiteKernel C α L J t) (interval A) := by
    simpa only [interval, uIcc_of_le (by linarith : -A ≤ A)] using
      (finiteKernel_section_ac C α L J t (-A) A).continuousOn
  exact hv1.continuousOn_mul hc isCompact_Icc

lemma native_quadratic_integrable {A L : ℝ} (hA : 0 < A) (hAL : A < L)
    {v : ℝ → ℝ} (hv : MemLp v 2 (physicalMeasure A)) (C α : ℝ) (J : ℕ) :
    IntegrableOn
      (fun t => nativeOperator A C α L J (primitive A v) t * primitive A v t)
      (interval A) := by
  have hf := nativeFlux_ac hA hAL hv C α J
  have hleft : AbsolutelyContinuousOnInterval
      (nativeFlux A C α L J (primitive A v)) (-A) 0 := by
    apply hf.mono
    rw [uIcc_of_le (by linarith : -A ≤ (0 : ℝ)),
      uIcc_of_le (by linarith : -A ≤ A)]
    intro t ht
    exact ⟨ht.1, le_trans ht.2 hA.le⟩
  have hright : AbsolutelyContinuousOnInterval
      (nativeFlux A C α L J (primitive A v)) 0 A := by
    apply hf.mono
    rw [uIcc_of_le hA.le, uIcc_of_le (by linarith : -A ≤ A)]
    intro t ht
    exact ⟨le_trans (by linarith : -A ≤ (0 : ℝ)) ht.1, ht.2⟩
  have hi := (primitive_test_left_integrable hA hv hleft).trans
    (primitive_test_right_integrable hA hv hright)
  have hi' : IntegrableOn (fun t => primitive A v t *
      deriv (nativeFlux A C α L J (primitive A v)) t) (interval A) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith : -A ≤ A)).mp hi
  apply hi'.neg.congr
  filter_upwards [nativeFlux_ae_deriv hA hAL hv C α J] with t ht
  simp only [ht, Pi.neg_apply]
  ring

lemma finiteKernel_outer_integrable {A L : ℝ} (hA : 0 < A) (hAL : A < L)
    {v : ℝ → ℝ} (hv : MemLp v 2 (physicalMeasure A)) (C α : ℝ) (J : ℕ) :
    IntegrableOn (fun t => ∫ u in interval A,
      finiteKernel C α L J t u * v u * v t) (interval A) := by
  have hv1 : IntegrableOn v (interval A) := hv.integrable (by norm_num)
  have hc : ContinuousOn (nativeFlux A C α L J (primitive A v)) (interval A) := by
    simpa only [interval, uIcc_of_le (by linarith : -A ≤ A)] using
      (nativeFlux_ac hA hAL hv C α J).continuousOn
  have hi := hv1.continuousOn_mul hc isCompact_Icc
  apply hi.congr
  exact Eventually.of_forall (fun t => by
    dsimp only
    rw [integral_mul_const, finiteKernel_first_parts hA hv C α L J t]
    change nativeFlux A C α L J (primitive A v) t * v t =
      firstFlux A C α L J (primitive A v) t * v t
    rw [firstFlux_eq_nativeFlux hA hAL hv C α J t])

theorem finite_J_identity_with_integrability {A L : ℝ} (hA : 0 < A) (hAL : A < L)
    {v : ℝ → ℝ} (hv : MemLp v 2 (physicalMeasure A)) (C α : ℝ) (J : ℕ) :
    (∀ t, IntegrableOn (fun u => finiteKernel C α L J t u * v u) (interval A)) ∧
    IntegrableOn (fun t => ∫ u in interval A,
      finiteKernel C α L J t u * v u * v t) (interval A) ∧
    IntegrableOn
      (fun t => nativeOperator A C α L J (primitive A v) t * primitive A v t)
      (interval A) ∧
    (∫ t in interval A, ∫ u in interval A, finiteKernel C α L J t u * v u * v t) =
    ∫ t in interval A,
      nativeOperator A C α L J (primitive A v) t * primitive A v t :=
  ⟨finiteKernel_row_integrable hA hv C α L J,
    finiteKernel_outer_integrable hA hAL hv C α J,
    native_quadratic_integrable hA hAL hv C α J,
    finite_J_Schur_identity hA hAL hv C α J⟩

end RhAnchored
#print axioms RhAnchored.finite_J_identity_with_integrability
