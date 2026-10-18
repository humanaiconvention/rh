import RhPulledCompleteForm001
import RhNativeCompleteDictionary001
import RhCompleteDilationDictionary001

/-! Exact native physical dictionary for the genuine common-domain pulled
form and its full signed perturbation. The physical test at the larger
radius is arbitrary; its exact primitive pullback labels the fixed core.
No positive margin, error estimate or cancellation inequality is assumed.
-/
noncomputable section
open Set MeasureTheory Filter FourierTransform
open scoped Topology BigOperators ENNReal
namespace RhPulledPhysicalDictionary
open RhAnchored RhAllPrime RhDilation RhDilationRank
open RhWeightedMeasureEmbedding RhWeightedPrimitiveLift RhFlatSmoothCore
open RhNativeCompleteBilinear RhPulledCompleteForm RhCompleteFormBound

lemma complex_dilate_extension {R r : ℝ} (hr : 0 < r) (w : ℝ → ℝ) :
    complexDilate r (RhTail.complexExtension R w) =
      RhTail.complexExtension (r * R) (dilate r w) := by
  funext t
  simp only [complexDilate, RhTail.complexExtension]
  rw [zeroExtension_dilate hr]
  simp only [dilate, Complex.ofReal_mul]

/-- Actual dilation of the small pulled-back anchored primitive reconstructs
the original large physical primitive as a weighted vector, not pointwise
Fourier data. All quotient changes occur almost everywhere. -/
theorem outward_actual_pullback {R r : ℝ} (hr : 1 ≤ r) (hR : 0 < R)
    {v : ℝ → ℝ} (hv : MemLp v 2 (physicalMeasure (r * R))) :
    (RhFlatCoreDilation.outwardMap hr
      (actualFlatCoreLift hR (pullback r v) (pullback_memLp (by linarith : 0 < r) hv)) : WeightedSpace) =
      actualPrimitiveLift (mul_pos (by linarith : 0 < r) hR) v hv := by
  have hr0 : 0 < r := by linarith
  let hs : MemLp (pullback r v) 2 (physicalMeasure R) := pullback_memLp hr0 hv
  let F := actualFlatCoreLift hR (pullback r v) hs
  let w := primitive R (pullback r v)
  apply physicalEmbedding_injective
  rw [actualPrimitiveLift_physical]
  apply Lp.ext
  have h := RhFlatCoreDilation.outwardMap_physical_ae hr F
  have hsmall : physicalEmbedding (F : WeightedSpace) =
      RhTail.physicalFourierVector R w (primitive_memLp hs) :=
    actualPrimitiveLift_physical hR (pullback r v) hs
  rw [hsmall] at h
  have he : RhTail.physicalFourierVector R w (primitive_memLp hs) =ᵐ[volume]
      RhTail.complexExtension R w := (RhTail.complexExtension_memLp (primitive_memLp hs)).coeFn_toLp
  have hscaled := h.trans (RhWeightedDilationInverse.complexDilate_congr_ae hr0 he)
  have hw : dilate r w = primitive (r * R) v := by
    funext t
    exact dilate_primitive_pullback hr0 R v t
  rw [complex_dilate_extension hr0, hw] at hscaled
  have hlarge : RhTail.physicalFourierVector (r * R) (primitive (r * R) v) (primitive_memLp hv) =ᵐ[volume]
      RhTail.complexExtension (r * R) (primitive (r * R) v) :=
    (RhTail.complexExtension_memLp (primitive_memLp hv)).coeFn_toLp
  exact hscaled.trans hlarge.symm

lemma baseForm_actual {R : ℝ} (hR : 0 < R) {v : ℝ → ℝ}
    (hv : MemLp v 2 (physicalMeasure R)) (N : ℕ) :
    baseForm R archConstant N (actualFlatCoreLift hR v hv) (actualFlatCoreLift hR v hv) =
      kernelQuadratic R (completeKernel N) v :=
  RhNativeCompleteDictionary.completeForm_actual hR hv N

/-- The actual transported continuous form has the exact physical diagonal. -/
theorem pulledForm_actual {R r : ℝ} (hr : 1 ≤ r) (hR : 0 < R)
    {v : ℝ → ℝ} (hv : MemLp v 2 (physicalMeasure (r * R))) (N : ℕ) :
    let F := actualFlatCoreLift hR (pullback r v) (pullback_memLp (by linarith : 0 < r) hv)
    pulledForm hr archConstant N F F = kernelQuadratic (r * R) (completeKernel N) v := by
  dsimp only
  simp only [pulledForm_apply, outward_actual_pullback hr hR hv]
  exact RhNativeCompleteDictionary.completeForm_actual (mul_pos (by linarith : 0 < r) hR) hv N

/-- The complete radius kernel is identified when the declared common
horizon contains EVERY active prime power, not merely a chosen prefix. -/
theorem pulledForm_actual_radius {R r : ℝ} (hr : 1 ≤ r) (hR : 0 < R)
    {v : ℝ → ℝ} (hv : MemLp v 2 (physicalMeasure (r * R))) (N : ℕ)
    (hN : radiusCutoff (r * R) ≤ N) :
    let F := actualFlatCoreLift hR (pullback r v) (pullback_memLp (by linarith : 0 < r) hv)
    pulledForm hr archConstant N F F = kernelQuadratic (r * R) (radiusKernel (r * R)) v := by
  dsimp only
  rw [pulledForm_actual hr hR hv N]
  exact (RhCompleteDilationDictionary.radius_quadratic_fixed_horizon
    (mul_pos (by linarith : 0 < r) hR).le N hN v).symm

/-- Fixed exact horizon, native scaled rank profiles and BOTH shifted delays. -/
theorem pulledForm_actual_native {R r : ℝ} (hr : 1 ≤ r) (hR : 0 < R)
    {v : ℝ → ℝ} (hv : MemLp v 2 (physicalMeasure (r * R))) (N : ℕ) :
    let hs : MemLp (pullback r v) 2 (physicalMeasure R) := pullback_memLp (by linarith : 0 < r) hv
    let F := actualFlatCoreLift hR (pullback r v) hs
    let w := primitive R (pullback r v)
    pulledForm hr archConstant N F F =
      actualArch (r * R) v hv - archConstant * mass R w + rankForm R r w -
      ∑ n ∈ Finset.Icc 2 N, weight n *
        (∫ t in interval R, primeShift R (Real.log (n : ℝ) / r) w t * w t) := by
  dsimp only
  rw [pulledForm_actual hr hR hv N]
  exact RhCompleteDilationDictionary.complete_cutoff_dilation_dictionary
    (by linarith : 0 < r) hR hv N

/-- Full signed actual diagonal perturbation. The common scalar cancels by the
EXACT physical dilation identity; both rank profiles and every old/new finite
prime delay remain. No separate absolute estimates or inverse loss is hidden. -/
theorem differenceForm_actual_native {R r : ℝ} (hr : 1 ≤ r) (hR : 0 < R)
    {v : ℝ → ℝ} (hv : MemLp v 2 (physicalMeasure (r * R))) (N : ℕ) :
    let hs : MemLp (pullback r v) 2 (physicalMeasure R) := pullback_memLp (by linarith : 0 < r) hv
    let F := actualFlatCoreLift hR (pullback r v) hs
    let w := primitive R (pullback r v)
    differenceForm hr archConstant N F F =
      (actualArch (r * R) v hv - actualArch R (pullback r v) hs) +
      (rankForm R r w - rankForm R 1 w) -
      ∑ n ∈ Finset.Icc 2 N, weight n *
        ((∫ t in interval R, primeShift R (Real.log (n : ℝ) / r) w t * w t) -
         (∫ t in interval R, primeShift R (Real.log (n : ℝ)) w t * w t)) := by
  dsimp only
  rw [differenceForm_apply, pulledForm_actual_native hr hR hv N,
    baseForm_actual hR (pullback_memLp (by linarith : 0 < r) hv) N,
    actual_complete_decomposition hR (pullback_memLp (by linarith : 0 < r) hv) N]
  unfold RhCompleteFormBound.boundedPart
  rw [RhCompleteDilationDictionary.rankScalar_as_rankForm]
  simp only [mul_sub, Finset.sum_sub_distrib]
  ring

end RhPulledPhysicalDictionary
#print axioms RhPulledPhysicalDictionary.outward_actual_pullback
#print axioms RhPulledPhysicalDictionary.pulledForm_actual
#print axioms RhPulledPhysicalDictionary.pulledForm_actual_radius
#print axioms RhPulledPhysicalDictionary.pulledForm_actual_native
#print axioms RhPulledPhysicalDictionary.differenceForm_actual_native
