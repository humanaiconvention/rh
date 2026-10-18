import RhNativeEndpointGluing001
import RhNativeStrictInteriorUCP001

/-! At a HYPOTHETICAL nonzero old radical, its total outward collar equations
cannot both vanish. This uses the exact finite-point gluing and full native
strict-interior uniqueness, not an isolated arithmetic component estimate.
No nonzero old radical is asserted to exist, and no numerical flux size is
claimed. -/
noncomputable section
open Set MeasureTheory
namespace RhNativeCollarNonvanishing
open RhAnchored RhWeightedMeasureEmbedding RhFlatSmoothCore RhNativeCompleteBilinear
open RhPuncturedFunctional RhEndpointWeakGluing RhNativeEndpointGluing

theorem not_both_collar_equations {R S : ℝ} (hR : 0 < R) (hRS : R < S)
    (C : ℝ) (N : ℕ) (p : FlatCoreSpace R) (hp : p ≠ 0)
    (hnull : ∀ Y : FlatCoreSpace R,
      completeForm R C N (p : WeightedSpace) (Y : WeightedSpace) = 0) :
    ¬ (VanishesOnSmooth S (Ioo (-S) (-R)) (nativeRow S C N (p : WeightedSpace)) ∧
       VanishesOnSmooth S (Ioo R S) (nativeRow S C N (p : WeightedSpace))) := by
  rintro ⟨hl,hr⟩
  apply hp
  apply RhNativeStrictInteriorUCP.full_row_unique hR hRS C N p
  exact old_null_and_collars_full_null hR hRS C N p hnull hl hr

/-- Exact actual radius cutoffs, with all newly activated prime-power rows. -/
theorem native_not_both_collar_equations {R S : ℝ} (hR : 0 < R) (hRS : R < S)
    (p : FlatCoreSpace R) (hp : p ≠ 0)
    (hnull : ∀ Y : FlatCoreSpace R,
      completeForm R archConstant (RhAllPrime.radiusCutoff R)
        (p : WeightedSpace) (Y : WeightedSpace) = 0) :
    ¬ (VanishesOnSmooth S (Ioo (-S) (-R))
          (nativeRow S archConstant (RhAllPrime.radiusCutoff S) (p : WeightedSpace)) ∧
       VanishesOnSmooth S (Ioo R S)
          (nativeRow S archConstant (RhAllPrime.radiusCutoff S) (p : WeightedSpace))) := by
  rintro ⟨hl,hr⟩
  apply hp
  apply RhNativeStrictInteriorUCP.full_row_unique hR hRS archConstant
    (RhAllPrime.radiusCutoff S) p
  exact native_old_null_and_collars_full_null hR hRS p hnull hl hr

end RhNativeCollarNonvanishing
#print axioms RhNativeCollarNonvanishing.not_both_collar_equations
#print axioms RhNativeCollarNonvanishing.native_not_both_collar_equations
