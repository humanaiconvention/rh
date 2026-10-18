import RhSmoothDerivativeDictionary001
import RhRealSameWindowSmooth001
import RhFlatCoreReal001

/-! Actual positivity dictionary between the physical L2 kernel and the FULL
real complete form domain. No global positivity is proved or assumed silently.
Negative form vectors transfer to genuine strict-interior smooth derivatives. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology ContDiff
namespace RhSmoothPhysicalTransfer
open RhAnchored RhWeightedMeasureEmbedding RhWeightedPrimitiveLift
open RhNativeCompleteBilinear RhNativeCompleteDictionary RhFlatSmoothCore
open RhSmoothDerivativeDictionary RhRealSameWindowSmooth

/-- Negative complete-domain energy has a genuine smooth physical witness.
This is conditional on the negative energy; none is constructed for the native form. -/
theorem negative_form_has_smooth_derivative {R : ℝ} (hR : 0 < R) (N : ℕ)
    (F : FlatCoreSpace R)
    (hneg : completeForm R archConstant N (F : WeightedSpace) (F : WeightedSpace) < 0) :
    ∃ f : ℝ → ℝ, ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧
      tsupport f ⊆ Ioo (-R) R ∧
      kernelQuadratic R (RhAllPrime.completeKernel N) (deriv f) < 0 := by
  let Y : SupportedSpace R := ⟨(F : WeightedSpace), flatCore_supported R F.property⟩
  obtain ⟨f, X, hfS, hfC, hfT, hfA, hNorm⟩ :=
    real_same_window_smooth_approximation hR Y (RhFlatCoreReal.physical_im_zero F)
  have hX : Tendsto (fun n => (X n : WeightedSpace)) atTop (𝓝 (F : WeightedSpace)) :=
    tendsto_iff_norm_sub_tendsto_zero.mpr hNorm
  have hcont : Continuous (fun z : WeightedSpace => completeForm R archConstant N z z) :=
    (completeForm R archConstant N).continuous.clm_apply continuous_id
  have hval : Tendsto (fun n => completeForm R archConstant N (X n : WeightedSpace) (X n : WeightedSpace))
      atTop (𝓝 (completeForm R archConstant N (F : WeightedSpace) (F : WeightedSpace))) :=
    hcont.continuousAt.tendsto.comp hX
  obtain ⟨n, hn⟩ := (hval.eventually (eventually_lt_nhds hneg)).exists
  refine ⟨f n, hfS n, hfC n, hfT n, ?_⟩
  rw [← native_smooth_derivative_dictionary hR (hfS n) (hfT n) (X n : WeightedSpace) (hfA n) N]
  exact hn

/-- Exact finite-radius/native-cutoff positivity equivalence. Infinite-energy
L2 vectors are NOT inserted into the complete form; physical inputs enter
through their actual finite-energy anchored primitives. -/
theorem physical_positive_iff_complete_form_positive {R : ℝ} (hR : 0 < R) (N : ℕ) :
    (∀ v : ℝ → ℝ, MemLp v 2 (physicalMeasure R) →
      0 ≤ kernelQuadratic R (RhAllPrime.completeKernel N) v) ↔
    (∀ F : FlatCoreSpace R,
      0 ≤ completeForm R archConstant N (F : WeightedSpace) (F : WeightedSpace)) := by
  constructor
  · intro hpos F
    by_contra hn
    have hneg := lt_of_not_ge hn
    obtain ⟨f, hfS, _hfC, _hfT, hfneg⟩ := negative_form_has_smooth_derivative hR N F hneg
    exact (not_lt_of_ge (hpos (deriv f) (derivative_memLp hfS))) hfneg
  · intro hpos v hv
    have hh := hpos (actualFlatCoreLift hR v hv)
    change 0 ≤ completeForm R archConstant N
      (actualPrimitiveLift hR v hv) (actualPrimitiveLift hR v hv) at hh
    rw [completeForm_actual hR hv N] at hh
    exact hh

end RhSmoothPhysicalTransfer
#print axioms RhSmoothPhysicalTransfer.negative_form_has_smooth_derivative
#print axioms RhSmoothPhysicalTransfer.physical_positive_iff_complete_form_positive
