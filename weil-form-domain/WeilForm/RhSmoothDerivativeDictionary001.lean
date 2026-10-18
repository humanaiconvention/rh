import RhNativeCompleteDictionary001
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-! Genuine compact smooth primitives are actual native physical inputs via
their derivatives. The assigned value at zero is reconciled ONLY almost
everywhere; no mean-zero assumption is imposed on arbitrary physical tests. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology ContDiff
namespace RhSmoothDerivativeDictionary
open RhAnchored RhWeightedMeasureEmbedding RhWeightedPrimitiveLift
open RhNativeCompleteBilinear RhNativeCompleteDictionary

lemma derivative_memLp {R : ℝ} {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) :
    MemLp (deriv f) 2 (physicalMeasure R) :=
  RhDilationRank.continuous_memLp (hf.continuous_deriv (by simp))

lemma boundary_zero {R : ℝ} {f : ℝ → ℝ}
    (hs : tsupport f ⊆ Ioo (-R) R) : f (-R) = 0 ∧ f R = 0 := by
  constructor
  · by_contra hn
    have hh := (hs (subset_tsupport f hn)).1
    exact (lt_irrefl (-R)) hh
  · by_contra hn
    have hh := (hs (subset_tsupport f hn)).2
    exact (lt_irrefl R) hh

lemma derivative_zeroExtension {R : ℝ} {f : ℝ → ℝ}
    (hs : tsupport f ⊆ Ioo (-R) R) : zeroExtension R (deriv f) = deriv f := by
  apply indicator_eq_self.mpr
  intro t ht
  have h := hs (support_deriv_subset ht)
  exact ⟨h.1.le, h.2.le⟩

lemma primitive_derivative_point {R : ℝ} (hR : 0 < R) {f : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hs : tsupport f ⊆ Ioo (-R) R)
    {t : ℝ} (ht : t ≠ 0) : primitive R (deriv f) t = f t := by
  have hEnds := boundary_zero hs
  have hDiff : Differentiable ℝ f := hf.differentiable (by simp)
  have hCont : Continuous (deriv f) := (hf.continuous_deriv (by simp))
  by_cases hn : t < 0
  · rw [primitive_eq_left (deriv f) hn]
    unfold leftPrimitive
    rw [derivative_zeroExtension hs,
      intervalIntegral.integral_deriv_eq_sub (fun x _ => hDiff x) (hCont.intervalIntegrable _ _),
      hEnds.1, sub_zero]
  · have hp : 0 < t := lt_of_le_of_ne (le_of_not_gt hn) (Ne.symm ht)
    rw [primitive_eq_right (deriv f) hp]
    unfold rightPrimitive
    rw [derivative_zeroExtension hs,
      intervalIntegral.integral_deriv_eq_sub (fun x _ => hDiff x) (hCont.intervalIntegrable _ _),
      hEnds.2, sub_zero]

/-- Equality at t=0 is deliberately absent. -/
theorem primitive_derivative_ae {R : ℝ} (hR : 0 < R) {f : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hs : tsupport f ⊆ Ioo (-R) R) :
    primitive R (deriv f) =ᵐ[volume] f := by
  have hz : ∀ᵐ t : ℝ ∂volume, t ≠ 0 := by
    have h : volume ({0} : Set ℝ) = 0 := by simp
    rw [measure_eq_zero_iff_ae_notMem] at h
    simpa only [mem_singleton_iff] using h
  filter_upwards [hz] with t ht
  exact primitive_derivative_point hR hf hs ht

/-- Exact identification in the actual weighted quotient, not just equality
of one form evaluation. -/
theorem smooth_weighted_equals_primitive_lift {R : ℝ} (hR : 0 < R)
    {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (hs : tsupport f ⊆ Ioo (-R) R)
    (F : WeightedSpace)
    (hF : physicalEmbedding F =ᵐ[volume] fun t => (f t : ℂ)) :
    F = actualPrimitiveLift hR (deriv f) (derivative_memLp hf) := by
  apply physicalEmbedding_injective
  rw [actualPrimitiveLift_physical]
  apply Lp.ext
  have hv : RhTail.physicalFourierVector R (primitive R (deriv f))
      (primitive_memLp (derivative_memLp hf)) =ᵐ[volume]
      RhTail.complexExtension R (primitive R (deriv f)) :=
    (RhTail.complexExtension_memLp (primitive_memLp (derivative_memLp hf))).coeFn_toLp
  filter_upwards [hF, hv, primitive_derivative_ae hR hf hs] with t ht hv' hp
  rw [ht, hv']
  by_cases hi : t ∈ interval R
  · simp [RhTail.complexExtension, zeroExtension, hi, hp]
  · have hz : f t = 0 := by
      by_contra hn
      have hh := hs (subset_tsupport f hn)
      exact hi ⟨hh.1.le, hh.2.le⟩
    simp [RhTail.complexExtension, zeroExtension, hi, hz]

/-- A compact smooth complete-domain vector has exactly the native physical
kernel value of its actual derivative, at EVERY declared finite horizon. -/
theorem native_smooth_derivative_dictionary {R : ℝ} (hR : 0 < R)
    {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (hs : tsupport f ⊆ Ioo (-R) R)
    (F : WeightedSpace) (hF : physicalEmbedding F =ᵐ[volume] fun t => (f t : ℂ)) (N : ℕ) :
    completeForm R archConstant N F F =
      kernelQuadratic R (RhAllPrime.completeKernel N) (deriv f) := by
  rw [smooth_weighted_equals_primitive_lift hR hf hs F hF]
  exact completeForm_actual hR (derivative_memLp hf) N

end RhSmoothDerivativeDictionary
#print axioms RhSmoothDerivativeDictionary.primitive_derivative_ae
#print axioms RhSmoothDerivativeDictionary.smooth_weighted_equals_primitive_lift
#print axioms RhSmoothDerivativeDictionary.native_smooth_derivative_dictionary
