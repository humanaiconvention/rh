import RhClosedSmoothCore001
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

/-! An explicit source-domain interface: absolutely continuous zero-trace
functions with L2 derivative are actual anchored primitives a.e. Hence they
belong to the proved smooth complete-form closure. No abstract Sobolev type or
external spectral theorem is silently imported. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace RhSobolevPrimitiveBridge
open RhAnchored RhWeightedMeasureEmbedding RhWeightedEnergyIdentity RhClosedSmoothCore

lemma ac_zero_trace_primitive_point {R : ℝ} (hR : 0 < R) {f : ℝ → ℝ}
    (hf : AbsolutelyContinuousOnInterval f (-R) R)
    (hleft : f (-R) = 0) (hright : f R = 0)
    {t : ℝ} (ht : t ∈ interval R) (ht0 : t ≠ 0) :
    primitive R (deriv f) t = f t := by
  have hI : -R ≤ R := by linarith
  change -R ≤ t ∧ t ≤ R at ht
  by_cases hneg : t < 0
  · have hs : uIcc (-R) t ⊆ interval R := by
      rw [uIcc_of_le ht.1]
      exact Icc_subset_Icc le_rfl ht.2
    have hfa : AbsolutelyContinuousOnInterval f (-R) t := by
      apply hf.mono
      simpa only [uIcc_of_le hI, interval] using hs
    rw [primitive_eq_left (deriv f) hneg]
    unfold leftPrimitive
    have hcongr : (∫ u in (-R)..t, zeroExtension R (deriv f) u) =
        ∫ u in (-R)..t, deriv f u := by
      apply intervalIntegral.integral_congr
      intro u hu
      exact zeroExtension_eq (hs hu)
    rw [hcongr, hfa.integral_deriv_eq_sub, hleft, sub_zero]
  · have hpos : 0 < t := lt_of_le_of_ne (le_of_not_gt hneg) (Ne.symm ht0)
    have hs : uIcc R t ⊆ interval R := by
      rw [uIcc_of_ge ht.2]
      exact Icc_subset_Icc ht.1 le_rfl
    have hfa : AbsolutelyContinuousOnInterval f R t := by
      apply hf.mono
      simpa only [uIcc_of_le hI, interval] using hs
    rw [primitive_eq_right (deriv f) hpos]
    unfold rightPrimitive
    have hcongr : (∫ u in R..t, zeroExtension R (deriv f) u) =
        ∫ u in R..t, deriv f u := by
      apply intervalIntegral.integral_congr
      intro u hu
      exact zeroExtension_eq (hs hu)
    rw [hcongr, hfa.integral_deriv_eq_sub, hright, sub_zero]

/-- Pointwise equality at zero is deliberately not asserted. -/
theorem ac_zero_trace_primitive_ae {R : ℝ} (hR : 0 < R) {f : ℝ → ℝ}
    (hf : AbsolutelyContinuousOnInterval f (-R) R)
    (hleft : f (-R) = 0) (hright : f R = 0) :
    primitive R (deriv f) =ᵐ[physicalMeasure R] f := by
  have hz : ∀ᵐ t : ℝ ∂volume, t ≠ 0 := by
    have h : volume ({0} : Set ℝ) = 0 := by simp
    rw [measure_eq_zero_iff_ae_notMem] at h
    simpa only [mem_singleton_iff] using h
  filter_upwards [ae_restrict_of_ae hz, ae_restrict_mem measurableSet_Icc] with t ht0 ht
  exact ac_zero_trace_primitive_point hR hf hleft hright ht ht0

/-- The standard one-dimensional H0^1 representative conditions put f in the
actual complete-form core. No density theorem is supplied as a hypothesis. -/
theorem ac_l2_zero_trace_has_actual_core_lift {R : ℝ} (hR : 0 < R)
    {f : ℝ → ℝ} (hf : AbsolutelyContinuousOnInterval f (-R) R)
    (hleft : f (-R) = 0) (hright : f R = 0)
    (hd : MemLp (deriv f) 2 (physicalMeasure R)) :
    ∃ X : CoreSpace R,
      physicalEmbedding ((X : SupportedSpace R) : WeightedSpace) =ᵐ[volume]
        fun t => ((zeroExtension R f t : ℝ) : ℂ) := by
  refine ⟨actualCoreLift hR (deriv f) hd, ?_⟩
  rw [actualCoreLift_physical]
  have hp : RhTail.physicalFourierVector R (primitive R (deriv f)) (primitive_memLp hd)
      =ᵐ[volume] RhTail.complexExtension R (primitive R (deriv f)) :=
    (RhTail.complexExtension_memLp (primitive_memLp hd)).coeFn_toLp
  have hz := (ac_zero_trace_primitive_ae hR hf hleft hright)
  have he : zeroExtension R (primitive R (deriv f)) =ᵐ[volume] zeroExtension R f := by
    unfold zeroExtension
    exact (ae_restrict_iff' measurableSet_Icc).mp hz |>.mono (fun t ht => by
      by_cases h : t ∈ interval R
      · simp only [indicator_of_mem h, ht h]
      · simp only [indicator_of_notMem h])
  filter_upwards [hp, he] with t ht hte
  rw [ht]
  change ((zeroExtension R (primitive R (deriv f)) t : ℝ) : ℂ) = _
  rw [hte]

end RhSobolevPrimitiveBridge
#print axioms RhSobolevPrimitiveBridge.ac_zero_trace_primitive_ae
#print axioms RhSobolevPrimitiveBridge.ac_l2_zero_trace_has_actual_core_lift
