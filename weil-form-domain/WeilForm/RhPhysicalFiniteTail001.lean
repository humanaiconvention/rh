import RhPhysicalPlancherel001
import RhFullKernelLimit001

noncomputable section
open Set MeasureTheory Filter FourierTransform
open scoped Topology BigOperators ENNReal
namespace RhAnchored

lemma nativeOperator_succ (A C α L : ℝ) (J : ℕ) (w : ℝ → ℝ) (t : ℝ) :
    nativeOperator A C α L (J+1) w t = nativeOperator A C α L J w t+
      (2/beta J)*w t-exponentialOperator A (beta J) w t := by
  unfold nativeOperator nativeDiagonal
  rw [Finset.sum_range_succ, Finset.sum_range_succ, archIndex_inv_eq_two_beta_inv]
  simp only [div_eq_mul_inv]
  ring

lemma finiteQuadratic_succ {A L : ℝ} (hA : 0 < A) (hAL : A < L)
    {v : ℝ → ℝ} (hv : MemLp v 2 (physicalMeasure A)) (C α : ℝ) (J : ℕ) :
    finiteQuadratic A C α L (J+1) v = finiteQuadratic A C α L J v+
      ∫ ξ : ℝ, RhTail.multiplier (RhTail.angularSquare ξ) (beta J)*
        RhTail.spectralDensity
          (RhTail.physicalFourierVector A (primitive A v) (primitive_memLp hv)) ξ := by
  have hw := primitive_memLp hv
  have hiSq := RhTail.physical_square_integrable hw
  have hiE := RhTail.physical_exponential_pair_integrable (beta_pos J).le hw
  have hiD : IntegrableOn (fun t => (2/beta J)*(primitive A v t)^2-
      exponentialOperator A (beta J) (primitive A v) t*primitive A v t) (interval A) :=
    (hiSq.const_mul (2/beta J)).sub hiE
  have hJ : finiteQuadratic A C α L J v =
      ∫ t in interval A, nativeOperator A C α L J (primitive A v) t*primitive A v t :=
    finite_J_Schur_identity hA hAL hv C α J
  have hJ1 : finiteQuadratic A C α L (J+1) v =
      ∫ t in interval A, nativeOperator A C α L (J+1) (primitive A v) t*primitive A v t :=
    finite_J_Schur_identity hA hAL hv C α (J+1)
  have hdiff : (∫ t in interval A,
      (2/beta J)*(primitive A v t)^2-
        exponentialOperator A (beta J) (primitive A v) t*primitive A v t) =
      ∫ ξ : ℝ, RhTail.multiplier (RhTail.angularSquare ξ) (beta J)*
        RhTail.spectralDensity (RhTail.physicalFourierVector A (primitive A v) hw) ξ := by
    rw [integral_sub (hiSq.const_mul _) hiE, integral_const_mul]
    exact RhTail.physical_exponential_plancherel (beta_pos J) hw
  rw [hJ1, hJ, ← hdiff, ← integral_add (native_quadratic_integrable hA hAL hv C α J) hiD]
  apply integral_congr_ae
  exact Eventually.of_forall (fun t => by
    dsimp only
    rw [nativeOperator_succ]
    ring)

theorem finite_physical_tail {A L : ℝ} (hA : 0 < A) (hAL : A < L)
    {v : ℝ → ℝ} (hv : MemLp v 2 (physicalMeasure A)) (C α : ℝ) (J K : ℕ) :
    finiteQuadratic A C α L (J+K) v = finiteQuadratic A C α L J v+
      ∑ k ∈ Finset.range K, ∫ ξ : ℝ,
        RhTail.multiplier (RhTail.angularSquare ξ) (beta (J+k))*
          RhTail.spectralDensity
            (RhTail.physicalFourierVector A (primitive A v) (primitive_memLp hv)) ξ := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Nat.add_succ, finiteQuadratic_succ hA hAL hv C α (J+K), ih, Finset.sum_range_succ]
    ring

lemma beta_add (J k : ℕ) : beta (J+k)=beta J+2*(k : ℝ) := by
  unfold beta archIndex
  push_cast
  ring

end RhAnchored
#print axioms RhAnchored.finite_physical_tail
