import RhTranslatedCoreRadical001
import RhNativeRadicalFinite001
import RhLocalPhysicalTranslation001
import RhConditionalWeakNullUCP001

/-! Strict-interior weak-null uniqueness for the ACTUAL complete finite-horizon
native form. No positivity is assumed. Local translates lie in an actual
finite-dimensional intermediate radical; the actual physical local orbit
cannot be finite dimensional unless the compact vector is zero.
This does not exclude a null at its OWN support radius and proves no RH claim.
-/
noncomputable section
set_option maxHeartbeats 180000
set_option synthInstance.maxHeartbeats 20000
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace RhNativeStrictInteriorUCP
open RhWeightedMeasureEmbedding RhFlatSmoothCore RhNativeCompleteBilinear
open RhPulledCompleteForm RhTranslatedCoreRadical RhNativeRadicalFinite
open RhLocalPhysicalTranslation RhLocalTranslationSpan RhNativeCompactGap

/-- A complete row null on a strictly LARGER support window cannot come from
any nonzero actual vector with the strictly smaller support. -/
theorem full_row_unique {R S : ℝ} (hR : 0 < R) (hRS : R < S)
    (C : ℝ) (N : ℕ) (p : FlatCoreSpace R)
    (hnull : ∀ g : FlatCoreSpace S,
      completeForm S C N (p : WeightedSpace) (g : WeightedSpace) = 0) : p = 0 := by
  classical
  by_contra hp
  let T : ℝ := (R+S)/2
  have hRT : R < T := by dsimp [T]; linarith
  have hTS : T < S := by dsimp [T]; linarith
  have hT : 0 < T := hR.trans hRT
  let eps : ℝ := min (T-R) (S-T)
  have heps : 0 < eps := lt_min (sub_pos.mpr hRT) (sub_pos.mpr hTS)
  let K := (baseForm T C N).ker
  letI : FiniteDimensional ℝ K := finite_base_radical hT C N
  let j : K →ₗ[ℝ] WholeSpace := (physical T).toLinearMap.comp K.subtype
  letI : FiniteDimensional ℝ j.range := Module.Finite.range j
  let u : WholeSpace := physicalEmbedding (p : WeightedSpace)
  have hu : RhTranslationSupport.Supported R u :=
    (mem_supportedSubspace_iff R (p : WeightedSpace)).mp (flatCore_supported R p.property)
  have hune : u ≠ 0 := by
    intro hz
    apply hp
    apply Subtype.ext
    change (p : WeightedSpace) = (0 : WeightedSpace)
    apply physicalEmbedding_injective
    rw [map_zero]
    exact hz
  have hle : localSpan action u eps ≤ j.range := by
    apply Submodule.span_le.mpr
    rintro x ⟨a,ha,rfl⟩
    have haa : |a| < min (T-R) (S-T) := abs_lt.mpr ha
    obtain ⟨hpT,hker,hphys⟩ := local_radical_translation hR hRT hTS C N p hnull a haa
    refine ⟨⟨translatedCore hT p a hpT,hker⟩,?_⟩
    exact hphys
  letI : FiniteDimensional ℝ (localSpan action u eps) :=
    FiniteDimensional.of_injective (Submodule.inclusion hle)
      (Submodule.inclusion_injective hle)
  exact not_finite_local_span u hu hune heps inferInstance

/-- Smooth weak-null tests determine the actual complete row. No finite-jet
representation or point evaluation on L2 classes is used. -/
theorem full_row_of_smooth {S : ℝ} (C : ℝ) (N : ℕ) (p : WeightedSpace)
    (hnull : ∀ f : ℝ → ℝ, ContDiff ℝ ∞ f → HasCompactSupport f →
      tsupport f ⊆ Ioo (-S) S → ∀ F : WeightedSpace,
      (physicalEmbedding F =ᵐ[volume] fun t => (f t : ℂ)) →
      completeForm S C N p F = 0) :
    ∀ g : FlatCoreSpace S, completeForm S C N p (g : WeightedSpace) = 0 := by
  have hspan : Submodule.span ℝ (smoothWeightedSet S) ≤ (completeForm S C N p).ker := by
    apply Submodule.span_le.mpr
    intro F hF
    obtain ⟨f,hf,hc,hs,hA⟩ := hF
    exact hnull f hf hc hs F hA
  have hall : flatCore S ≤ (completeForm S C N p).ker :=
    (Submodule.span ℝ (smoothWeightedSet S)).topologicalClosure_minimal hspan
      (completeForm S C N p).isClosed_ker
  intro g
  exact hall g.property

/-- The previously explicit combined-UCP premise is now discharged for any
strict support enlargement, every finite N, and the actual native scalar. -/
theorem combined_weak_ucp {R S : ℝ} (hR : 0 < R) (hRS : R < S) (N : ℕ) :
    RhConditionalWeakNullUCP.CombinedWeakUCP R S N := by
  intro p hp
  apply full_row_unique hR hRS RhAnchored.archConstant N p
  exact full_row_of_smooth RhAnchored.archConstant N (p : WeightedSpace) hp

end RhNativeStrictInteriorUCP
#print axioms RhNativeStrictInteriorUCP.full_row_unique
#print axioms RhNativeStrictInteriorUCP.full_row_of_smooth
#print axioms RhNativeStrictInteriorUCP.combined_weak_ucp
