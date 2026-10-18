import RhNativeNullFluxPhysical001

/-! Direction audit for a hypothetical combined weak-null uniqueness theorem.
The uniqueness premise is explicit and UNPROVED here. It implies strict
outward failure from an old nonzero zero diagonal, not its continuation. -/
noncomputable section
open Set MeasureTheory
open scoped ContDiff
namespace RhConditionalWeakNullUCP
open RhAnchored RhWeightedMeasureEmbedding RhFlatSmoothCore RhNativeCompleteBilinear

/-- Complete native weak equation on all genuine smooth tests in the larger
open window. The ambient row includes both ranks and every finite shift. -/
def SmoothWeakNull (S : ℝ) (N : ℕ) (p : WeightedSpace) : Prop :=
  ∀ f : ℝ → ℝ, ContDiff ℝ ∞ f → HasCompactSupport f →
    tsupport f ⊆ Ioo (-S) S →
    ∀ F : WeightedSpace, (physicalEmbedding F =ᵐ[volume] fun t => (f t : ℂ)) →
      completeForm S archConstant N p F = 0

/-- This is a proposed uniqueness statement, not an established native fact. -/
def CombinedWeakUCP (R S : ℝ) (N : ℕ) : Prop :=
  ∀ p : FlatCoreSpace R, SmoothWeakNull S N (p : WeightedSpace) → p = 0

/-- A combined UCP would force an actual complete outward cross pairing to be
nonzero for every nonzero old zero vector. It cannot justify radical inheritance. -/
theorem nonzero_cross_of_combined_ucp {R S : ℝ} (N : ℕ)
    (hucp : CombinedWeakUCP R S N) (p : FlatCoreSpace R) (hp : p ≠ 0) :
    ∃ g : FlatCoreSpace S,
      completeForm S archConstant N (p : WeightedSpace) (g : WeightedSpace) ≠ 0 := by
  classical
  have hex : ∃ (f : ℝ → ℝ), ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧
      tsupport f ⊆ Ioo (-S) S ∧ ∃ F : WeightedSpace,
        (physicalEmbedding F =ᵐ[volume] fun t => (f t : ℂ)) ∧
        completeForm S archConstant N (p : WeightedSpace) F ≠ 0 := by
    by_contra hn
    apply hp
    apply hucp p
    intro f hf hc hs F hF
    by_contra hb
    exact hn ⟨f, hf, hc, hs, F, hF, hb⟩
  obtain ⟨f, hf, hc, hs, F, hF, hb⟩ := hex
  let g : FlatCoreSpace S := ⟨F, smooth_generator_mem ⟨f, hf, hc, hs, hF⟩⟩
  exact ⟨g, hb⟩

/-- Literal support inclusion preserves the old zero diagonal. Therefore the
NONZERO cross term forced by a combined UCP gives a strictly negative actual
physical smooth-derivative witness in the larger support. The UCP premise is
not proved, and no actual old zero vector is asserted to exist. -/
theorem combined_ucp_forces_outward_negative {R S : ℝ}
    (hRS : R < S) (hS : 0 < S) (N : ℕ)
    (hucp : CombinedWeakUCP R S N) (p : FlatCoreSpace R) (hp : p ≠ 0)
    (hdiag : completeForm R archConstant N (p : WeightedSpace) (p : WeightedSpace) = 0) :
    ∃ f : ℝ → ℝ, ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧
      tsupport f ⊆ Ioo (-S) S ∧
      kernelQuadratic S (RhAllPrime.completeKernel N) (deriv f) < 0 := by
  obtain ⟨g, hg⟩ := nonzero_cross_of_combined_ucp N hucp p hp
  exact RhNativeNullFluxPhysical.complete_flux_nonzero_gives_physical_negative
    hRS.le hS N p g hdiag hg

end RhConditionalWeakNullUCP
#print axioms RhConditionalWeakNullUCP.nonzero_cross_of_combined_ucp
#print axioms RhConditionalWeakNullUCP.combined_ucp_forces_outward_negative
