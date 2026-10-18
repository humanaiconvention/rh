import RhEndpointWeakGluing001
import RhLiteralSupportForm001
import RhCompleteFormHorizon001

/-! PRIVATE exact native endpoint gluing. Old full nullity supplies the
interior equation. BOTH total collar equations remain explicit, unproved
arithmetic inputs. A common sufficient finite cap keeps all prime companions.
No point-supported residual, ambient extension or positivity premise is used.
-/
set_option maxHeartbeats 150000
noncomputable section
open Set MeasureTheory
open scoped Topology ContDiff
namespace RhNativeEndpointGluing
open RhAnchored RhWeightedMeasureEmbedding RhFlatSmoothCore RhNativeCompleteBilinear
open RhPuncturedFunctional RhEndpointWeakGluing RhLiteralSupportForm RhCompleteFormHorizon

/-- Literal old support identifies the exact interior row, with the same cap. -/
theorem old_interior_row_vanishes {R S : ℝ} (hRS : R ≤ S)
    (C : ℝ) (N : ℕ) (p : FlatCoreSpace R)
    (hnull : ∀ Y : FlatCoreSpace R,
      completeForm R C N (p : WeightedSpace) (Y : WeightedSpace) = 0) :
    VanishesOnSmooth S (Ioo (-R) R) (nativeRow S C N (p : WeightedSpace)) := by
  intro f hf hc hs X hX
  have hxold : (X : WeightedSpace) ∈ flatCore R := smooth_generator_mem ⟨f,hf,hc,hs,hX⟩
  let Y : FlatCoreSpace R := ⟨(X : WeightedSpace),hxold⟩
  change completeForm S C N (p : WeightedSpace) (X : WeightedSpace) = 0
  rw [←completeForm_support_invariant hRS C N (p : WeightedSpace) (X : WeightedSpace)
    (flatCore_supported R p.property) (flatCore_supported R hxold)]
  exact hnull Y

/-- The actual whole old radical persists in the larger complete form IF
its complete total two-collar flux vanishes. No component is substituted. -/
theorem old_null_and_collars_full_null {R S : ℝ} (hR : 0 < R) (hRS : R < S)
    (C : ℝ) (N : ℕ) (p : FlatCoreSpace R)
    (hnull : ∀ Y : FlatCoreSpace R,
      completeForm R C N (p : WeightedSpace) (Y : WeightedSpace) = 0)
    (hl : VanishesOnSmooth S (Ioo (-S) (-R)) (nativeRow S C N (p : WeightedSpace)))
    (hr : VanishesOnSmooth S (Ioo R S) (nativeRow S C N (p : WeightedSpace))) :
    ∀ X : FlatCoreSpace S,
      completeForm S C N (p : WeightedSpace) (X : WeightedSpace) = 0 :=
  native_row_zero_of_three_regions hR hRS C N (p : WeightedSpace) hl
    (old_interior_row_vanishes hRS.le C N p hnull) hr

/-- Exact ALL-ACTIVE native cap at each radius: the old null equation is
transported to the larger finite cap by the already proved horizon identity.
The scalar is the literal native archConstant. The collar equations are not
proved here; once supplied there is no extra endpoint-distribution obligation.
-/
theorem native_old_null_and_collars_full_null {R S : ℝ} (hR : 0 < R) (hRS : R < S)
    (p : FlatCoreSpace R)
    (hnull : ∀ Y : FlatCoreSpace R,
      completeForm R archConstant (RhAllPrime.radiusCutoff R)
        (p : WeightedSpace) (Y : WeightedSpace) = 0)
    (hl : VanishesOnSmooth S (Ioo (-S) (-R))
      (nativeRow S archConstant (RhAllPrime.radiusCutoff S) (p : WeightedSpace)))
    (hr : VanishesOnSmooth S (Ioo R S)
      (nativeRow S archConstant (RhAllPrime.radiusCutoff S) (p : WeightedSpace))) :
    ∀ X : FlatCoreSpace S,
      completeForm S archConstant (RhAllPrime.radiusCutoff S)
        (p : WeightedSpace) (X : WeightedSpace) = 0 := by
  have hcR : CoversActive R (RhAllPrime.radiusCutoff R) := coversActive_of_radiusCutoff le_rfl
  have hcS : CoversActive R (RhAllPrime.radiusCutoff S) :=
    coversActive_mono_radius hRS.le (coversActive_of_radiusCutoff le_rfl)
  have hnullcap : ∀ Y : FlatCoreSpace R,
      completeForm R archConstant (RhAllPrime.radiusCutoff S)
        (p : WeightedSpace) (Y : WeightedSpace) = 0 := by
    intro Y
    rw [←completeForm_horizon_eq archConstant hcR hcS
      (flatCore_supported R p.property) (flatCore_supported R Y.property)]
    exact hnull Y
  exact old_null_and_collars_full_null hR hRS archConstant (RhAllPrime.radiusCutoff S)
    p hnullcap hl hr

end RhNativeEndpointGluing
#print axioms RhNativeEndpointGluing.old_interior_row_vanishes
#print axioms RhNativeEndpointGluing.old_null_and_collars_full_null
#print axioms RhNativeEndpointGluing.native_old_null_and_collars_full_null