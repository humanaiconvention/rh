import RhWeightedPrimitiveLift001
import RhActualSmoothFormClosure001

/-!
Literal smooth approximation inside the concrete supported weighted Hilbert
space. The sequence is constructed from the accepted actual native smooth
approximation theorem and the proved weighted energy identity. No norm
convergence or smooth-core density conclusion is assumed as an input.
-/
set_option maxHeartbeats 0
noncomputable section
open Set MeasureTheory Filter FourierTransform
open scoped Topology ContDiff BigOperators ENNReal
namespace RhActualWeightedClosure
open RhAnchored RhWeightedMeasureEmbedding RhWeightedEnergyIdentity RhWeightedPrimitiveLift
open RhActualSmoothFormClosure

/-- Every actual real physical primitive is a weighted Hilbert norm limit of
same-window genuine smooth compact representatives. The image assertions are
AE assertions about actual L2 quotients, not pointwise derivative identities. -/
theorem actual_smooth_weighted_approximation {R : ℝ} (hR : 0 < R)
    {v : ℝ → ℝ} (hv : MemLp v 2 (physicalMeasure R)) :
    ∃ (f : ℕ → ℝ → ℝ) (X : ℕ → SupportedSpace R),
      (∀ n, ContDiff ℝ ∞ (f n)) ∧ (∀ n, HasCompactSupport (f n)) ∧
      (∀ n, tsupport (f n) ⊆ Ioo (-R) R) ∧
      (∀ n, physicalEmbedding (X n : WeightedSpace) =ᵐ[volume] fun t => (f n t : ℂ)) ∧
      Tendsto (fun n => ‖X n - actualPrimitiveSupportedLift hR v hv‖) atTop (𝓝 0) := by
  obtain ⟨f, hfS, hfC, hfT, hfAE, hf, hFinite, hGraph, hShift⟩ :=
    actual_smooth_complete_form_approximation hR hv
  let uE (n : ℕ) : WholeSpace :=
    RhTail.physicalFourierVector R (approximationError R f v n) (hf n)
  let errorLift (n : ℕ) : SupportedSpace R :=
    ⟨frequencyLift (uE n) (hFinite n),
      frequencyLift_mem_supportedSubspace R (uE n) (hFinite n)
        (physicalVector_support (hf n))⟩
  let X (n : ℕ) : SupportedSpace R := actualPrimitiveSupportedLift hR v hv + errorLift n
  have hImage (n : ℕ) :
      physicalEmbedding (X n : WeightedSpace) =
        RhTail.physicalFourierVector R (primitive R v) (primitive_memLp hv) + uE n := by
    change physicalEmbedding (actualPrimitiveLift hR v hv + frequencyLift (uE n) (hFinite n)) = _
    rw [map_add, actualPrimitiveLift_physical, physicalEmbedding_frequencyLift]
  have hRawImage (n : ℕ) :
      physicalEmbedding (X n : WeightedSpace) =ᵐ[volume] fun t => (f n t : ℂ) := by
    rw [hImage n]
    have hp : RhTail.physicalFourierVector R (primitive R v) (primitive_memLp hv) =ᵐ[volume]
        RhTail.complexExtension R (primitive R v) :=
      (RhTail.complexExtension_memLp (primitive_memLp hv)).coeFn_toLp
    have he : uE n =ᵐ[volume] RhTail.complexExtension R (approximationError R f v n) :=
      (RhTail.complexExtension_memLp (hf n)).coeFn_toLp
    filter_upwards [Lp.coeFn_add
      (RhTail.physicalFourierVector R (primitive R v) (primitive_memLp hv)) (uE n), hp, he]
      with t ht hpt het
    rw [ht]
    simp only [Pi.add_apply]
    rw [hpt, het]
    by_cases htI : t ∈ interval R
    · simp only [RhTail.complexExtension, zeroExtension_eq htI]
      simp [approximationError, Pi.sub_apply]
    · have hft : f n t = 0 := by
        by_contra hn
        have hi := hfT n (subset_tsupport (f n) hn)
        apply htI
        exact ⟨hi.1.le, hi.2.le⟩
      simp [RhTail.complexExtension, zeroExtension, htI, hft]
  have hNormSq (n : ℕ) :
      ‖X n - actualPrimitiveSupportedLift hR v hv‖ ^ 2 =
        graphValue R (approximationError R f v n) (hf n) := by
    change ‖(actualPrimitiveSupportedLift hR v hv + errorLift n) -
      actualPrimitiveSupportedLift hR v hv‖ ^ 2 = _
    rw [add_sub_cancel_left]
    change ‖frequencyLift (uE n) (hFinite n)‖ ^ 2 = _
    rw [frequencyLift_norm_square]
    change ‖RhTail.physicalFourierVector R (approximationError R f v n) (hf n)‖ ^ 2 + _ = _
    rw [physicalVector_norm_square]
    unfold graphValue RhCompleteFormBound.mass
    ring
  have hNormSqZero : Tendsto
      (fun n => ‖X n - actualPrimitiveSupportedLift hR v hv‖ ^ 2) atTop (𝓝 0) := by
    simpa only [hNormSq] using hGraph
  have hNormZero : Tendsto
      (fun n => ‖X n - actualPrimitiveSupportedLift hR v hv‖) atTop (𝓝 0) := by
    have hs := Real.continuous_sqrt.continuousAt.tendsto.comp hNormSqZero
    simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using hs
  exact ⟨f, X, hfS, hfC, hfT, hRawImage, hNormZero⟩

end RhActualWeightedClosure
#print axioms RhActualWeightedClosure.actual_smooth_weighted_approximation
