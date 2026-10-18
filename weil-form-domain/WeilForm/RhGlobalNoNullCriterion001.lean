import RhNativeRadiusFamily001

/-! A conditional all-radius criterion, not all-radius positivity.
The arithmetic no-null statement is EXPLICIT and remains unproved.
No finite numerical margin is reused as an all-radius reserve. -/
noncomputable section
open Set MeasureTheory
open scoped Topology
namespace RhGlobalNoNullCriterion
open RhAnchored RhWeightedMeasureEmbedding RhFlatSmoothCore RhNativeCompleteBilinear
open RhNativeRadiusFamily RhNativeRayleighDomain RhNativeRayleighPositivity
open RhNativeCompactGap

/-- Exact unproved arithmetic condition: at any later nonnegative native
state the actual complete-form radical is trivial. -/
def NoNullNonnegativeStates (R0 C : ℝ) : Prop :=
  ∀ R : ℝ, R0 < R →
    (∀ F : FlatCoreSpace R, 0 ≤ completeForm R C (RhAllPrime.radiusCutoff R)
      (F : WeightedSpace) (F : WeightedSpace)) →
    ∀ F : FlatCoreSpace R,
      F ∈ (form R C (RhAllPrime.radiusCutoff R)).ker → F = 0

/-- Native positivity follows IF the stated all-radius arithmetic exclusion
is proved. This theorem does not discharge that hypothesis or a base gap. -/
theorem global_native_positive_of_no_null {R0 : ℝ} (hR0 : 0 < R0)
    (hbase : 0 < nativeBottom R0 archConstant)
    (hno : NoNullNonnegativeStates R0 archConstant) :
    ∀ R : ℝ, 0 < R → ∀ v : ℝ → ℝ, MemLp v 2 (physicalMeasure R) →
      0 ≤ kernelQuadratic R (RhAllPrime.radiusKernel R) v := by
  intro R hR
  apply (nativeBottom_nonnegative_iff_physical hR).mp
  by_cases hRR0 : R ≤ R0
  · exact hbase.le.trans (nativeBottom_antitone hR hRR0 archConstant)
  · have hR0R : R0 ≤ R := (lt_of_not_ge hRR0).le
    by_contra hh
    have hbad := lt_of_not_ge hh
    obtain ⟨S,hS0,_hSR,hzero,F,hF,hker⟩ :=
      native_sign_change_has_null hR0 hR0R archConstant hbase hbad
    have hpos := (bottom_nonnegative_iff (hR0.trans hS0)
      archConstant (RhAllPrime.radiusCutoff S)).mp hzero.ge
    exact hF (hno S hS0 hpos F hker)

end RhGlobalNoNullCriterion
#print axioms RhGlobalNoNullCriterion.global_native_positive_of_no_null
