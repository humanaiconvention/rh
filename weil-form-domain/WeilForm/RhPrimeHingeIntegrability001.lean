import RhPrimeHingeUnrestricted001
import RhDilationNativeSector001

/-! Genuine integrability and exact finite-list summation for unrestricted
anchored hinges. No support-window restriction A < L is used. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology BigOperators Interval
namespace RhPrimeHingeIntegrability
open RhAnchored RhSupportPrimeHinge RhPrimeHingeUnrestricted

lemma hinge_joint_continuous (alpha L : ℝ) :
    Continuous (fun p : ℝ × ℝ => primeHinge alpha L p.1 p.2) := by
  unfold primeHinge anchoredKernel
  fun_prop

lemma physical_row_integrable {A : ℝ} {v : ℝ → ℝ}
    (hv : MemLp v 2 (physicalMeasure A)) (alpha L t : ℝ) :
    IntegrableOn (fun u => primeHinge alpha L t u * v u) (interval A) := by
  have hv1 : IntegrableOn v (interval A) := hv.integrable (by norm_num)
  have hc : Continuous (fun u : ℝ => primeHinge alpha L t u) := by
    unfold primeHinge anchoredKernel
    fun_prop
  exact hv1.continuousOn_mul hc.continuousOn isCompact_Icc

theorem physical_integrand_integrable {A : ℝ} {v : ℝ → ℝ}
    (hv : MemLp v 2 (physicalMeasure A)) (alpha L : ℝ) :
    Integrable (fun p : ℝ × ℝ => primeHinge alpha L p.1 p.2 * v p.2 * v p.1)
      ((physicalMeasure A).prod (physicalMeasure A)) :=
  RhSupportLocalization.kernel_joint_integrable _ (hinge_joint_continuous alpha L) hv hv

lemma physical_outer_integrable {A L : ℝ} (hA : 0 < A) (hL : 0 < L)
    {v : ℝ → ℝ} (hv : MemLp v 2 (physicalMeasure A)) (alpha : ℝ) :
    IntegrableOn (fun t => ∫ u in interval A, primeHinge alpha L t u * v u * v t)
      (interval A) := by
  have hc : ContinuousOn (shiftFlux A L (primitive A v)) (interval A) := by
    simpa only [interval, uIcc_of_le (by linarith : -A ≤ A)] using
      (shiftFlux_ac hv L).continuousOn
  have hv1 : IntegrableOn v (interval A) := hv.integrable (by norm_num)
  have hi : IntegrableOn (fun t => shiftFlux A L (primitive A v) t * v t) (interval A) :=
    hv1.continuousOn_mul hc isCompact_Icc
  apply (hi.const_mul alpha).congr
  exact Eventually.of_forall (fun t => by
    dsimp only
    rw [integral_mul_const, RhPrimeHingeUnrestricted.physical_row_identity hA hL hv]
    ring)

lemma primitive_shift_integrable {A : ℝ} {v : ℝ → ℝ}
    (hv : MemLp v 2 (physicalMeasure A)) (L : ℝ) :
    IntegrableOn (fun t => primeShift A L (primitive A v) t * primitive A v t)
      (interval A) :=
  RhEndpointParity.shift_integrable (primitive_memLp hv) L

lemma kernelQuadratic_finset_sum {ι : Type*} (s : Finset ι)
    (K : ι → ℝ → ℝ → ℝ)
    (hK : ∀ i, Continuous (fun p : ℝ × ℝ => K i p.1 p.2))
    {A : ℝ} {v : ℝ → ℝ} (hv : MemLp v 2 (physicalMeasure A)) :
    kernelQuadratic A (fun t u => ∑ i ∈ s, K i t u) v =
      ∑ i ∈ s, kernelQuadratic A (K i) v := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [kernelQuadratic]
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    rw [RhDilationNative.kernelQuadratic_add (hK i)
      (continuous_finsetSum s (fun j _ => hK j)) hv, ih]

/-- Every delay and coefficient remains attached in the exact finite sum. -/
theorem finite_hinge_sum_identity {ι : Type*} (s : Finset ι)
    (alpha L : ι → ℝ) (hL : ∀ i ∈ s, 0 < L i)
    {A : ℝ} (hA : 0 < A) {v : ℝ → ℝ}
    (hv : MemLp v 2 (physicalMeasure A)) :
    kernelQuadratic A (fun t u => ∑ i ∈ s, primeHinge (alpha i) (L i) t u) v =
      -(∑ i ∈ s, alpha i * (∫ t in interval A,
        primeShift A (L i) (primitive A v) t * primitive A v t)) := by
  rw [kernelQuadratic_finset_sum s _ (fun i => hinge_joint_continuous (alpha i) (L i)) hv,
    ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [RhPrimeHingeUnrestricted.physical_primitive_identity hA (hL i hi) hv]
  ring

end RhPrimeHingeIntegrability
#print axioms RhPrimeHingeIntegrability.physical_integrand_integrable
#print axioms RhPrimeHingeIntegrability.physical_outer_integrable
#print axioms RhPrimeHingeIntegrability.primitive_shift_integrable
#print axioms RhPrimeHingeIntegrability.finite_hinge_sum_identity
