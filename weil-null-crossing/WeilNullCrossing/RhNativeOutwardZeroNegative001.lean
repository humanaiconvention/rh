import RhNativeStrictInteriorUCP001
import RhCompleteFormHorizon001

/-! Strict outward negative witnesses from a HYPOTHETICAL nonzero old exact
zero diagonal. The native strict-interior UCP premise is now discharged.
No zero state is constructed; this does not exclude first contact. -/
noncomputable section
open Set MeasureTheory
open scoped ContDiff
namespace RhNativeOutwardZeroNegative
open RhAnchored RhWeightedMeasureEmbedding RhFlatSmoothCore RhNativeCompleteBilinear
open RhNativeStrictInteriorUCP RhConditionalWeakNullUCP RhCompleteFormHorizon

/-- One exact finite cap on both windows; every prescribed signed companion
remains inside the native form. Every genuine strict enlargement admits a
smooth physical negative witness IF the old zero vector exists. -/
theorem fixed_horizon_outward_negative {R S : ℝ} (hR : 0 < R) (hRS : R < S)
    (N : ℕ) (p : FlatCoreSpace R) (hp : p ≠ 0)
    (hdiag : completeForm R archConstant N (p : WeightedSpace) (p : WeightedSpace) = 0) :
    ∃ f : ℝ → ℝ, ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧
      tsupport f ⊆ Ioo (-S) S ∧
      kernelQuadratic S (RhAllPrime.completeKernel N) (deriv f) < 0 := by
  exact combined_ucp_forces_outward_negative hRS (hR.trans hRS) N
    (combined_weak_ucp hR hRS N) p hp hdiag

/-- ACTUAL native cutoffs on both sides. For each larger S, its finite cutoff
is fixed first; exact horizon coherence transports the old native zero to
that same cap. No all-radius infinite arithmetic horizon is introduced. -/
theorem native_outward_negative {R S : ℝ} (hR : 0 < R) (hRS : R < S)
    (p : FlatCoreSpace R) (hp : p ≠ 0)
    (hdiag : completeForm R archConstant (RhAllPrime.radiusCutoff R)
      (p : WeightedSpace) (p : WeightedSpace) = 0) :
    ∃ f : ℝ → ℝ, ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧
      tsupport f ⊆ Ioo (-S) S ∧
      kernelQuadratic S (RhAllPrime.radiusKernel S) (deriv f) < 0 := by
  have hpS : (p : WeightedSpace) ∈ supportedSubspace R := flatCore_supported R p.property
  have he := bounded_radius_form_horizon hRS.le archConstant
    (N := RhAllPrime.radiusCutoff S) le_rfl hpS hpS
  have hz : completeForm R archConstant (RhAllPrime.radiusCutoff S)
      (p : WeightedSpace) (p : WeightedSpace) = 0 := he.symm.trans hdiag
  change ∃ f : ℝ → ℝ, ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧
    tsupport f ⊆ Ioo (-S) S ∧
    kernelQuadratic S (RhAllPrime.completeKernel (RhAllPrime.radiusCutoff S)) (deriv f) < 0
  exact fixed_horizon_outward_negative hR hRS (RhAllPrime.radiusCutoff S) p hp hz

end RhNativeOutwardZeroNegative
#print axioms RhNativeOutwardZeroNegative.fixed_horizon_outward_negative
#print axioms RhNativeOutwardZeroNegative.native_outward_negative

