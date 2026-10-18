import RhFlatSmoothCore001
import RhNativeCompleteDictionary001

/-! Literal support inclusion is NOT dilation. An old zero diagonal stays
exactly zero on a larger interval, retaining every finite prime companion.
No vanishing or nonvanishing of the ACTUAL exterior flux is inferred. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology BigOperators
namespace RhLiteralSupportForm
open RhAnchored RhWeightedMeasureEmbedding RhFlatSmoothCore RhNativeCompleteBilinear

lemma interval_subset {R S : ℝ} (hRS : R ≤ S) : interval R ⊆ interval S := by
  intro t ht
  exact ⟨by linarith [ht.1], by linarith [ht.2]⟩

theorem flatCore_mono {R S : ℝ} (hRS : R ≤ S) : flatCore R ≤ flatCore S := by
  apply (Submodule.span ℝ (smoothWeightedSet R)).topologicalClosure_minimal
  · apply Submodule.span_le.mpr
    rintro F ⟨f, hfS, hfC, hfT, hfA⟩
    apply smooth_generator_mem
    refine ⟨f, hfS, hfC, ?_, hfA⟩
    intro t ht
    have hi := hfT ht
    exact ⟨by linarith [hi.1], by linarith [hi.2]⟩
  · exact flatCore_isClosed S

lemma profileMoment_support_invariant {R S : ℝ} (hRS : R ≤ S)
    (f : ℝ → ℝ) (hfR : MemLp f 2 (physicalMeasure R))
    (hfS : MemLp f 2 (physicalMeasure S)) (F : WeightedSpace)
    (hF : F ∈ supportedSubspace R) :
    profileMoment R f hfR F = profileMoment S f hfS F := by
  change inner ℂ (RhTail.physicalFourierVector R f hfR) (physicalEmbedding F) =
    inner ℂ (RhTail.physicalFourierVector S f hfS) (physicalEmbedding F)
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  have hr : RhTail.physicalFourierVector R f hfR =ᵐ[volume] RhTail.complexExtension R f :=
    (RhTail.complexExtension_memLp hfR).coeFn_toLp
  have hs : RhTail.physicalFourierVector S f hfS =ᵐ[volume] RhTail.complexExtension S f :=
    (RhTail.complexExtension_memLp hfS).coeFn_toLp
  filter_upwards [hr, hs, (mem_supportedSubspace_iff R F).mp hF] with t htR htS htF
  rw [htR, htS]
  by_cases hi : t ∈ interval R
  · have hj := interval_subset hRS hi
    simp [RhTail.complexExtension, zeroExtension, hi, hj]
  · rw [htF hi]
    simp

lemma profilePair_support_invariant {R S : ℝ} (hRS : R ≤ S)
    (f : ℝ → ℝ) (hfR : MemLp f 2 (physicalMeasure R))
    (hfS : MemLp f 2 (physicalMeasure S)) (F G : WeightedSpace)
    (hF : F ∈ supportedSubspace R) (hG : G ∈ supportedSubspace R) :
    profilePair R f hfR F G = profilePair S f hfS F G := by
  change inner ℝ (profileMoment R f hfR F) (profileMoment R f hfR G) = _
  rw [profileMoment_support_invariant hRS f hfR hfS F hF,
    profileMoment_support_invariant hRS f hfR hfS G hG]
  rfl

/-- One exact finite horizon on BOTH sides; newly inactive shifts are not
removed and both rank profiles agree on the actual old support. -/
theorem completeForm_support_invariant {R S : ℝ} (hRS : R ≤ S)
    (C : ℝ) (N : ℕ) (F G : WeightedSpace)
    (hF : F ∈ supportedSubspace R) (hG : G ∈ supportedSubspace R) :
    completeForm R C N F G = completeForm S C N F G := by
  have hc := profilePair_support_invariant hRS (fun t => Real.cosh (t/2))
    (cosh_memLp R) (cosh_memLp S) F G hF hG
  have hs := profilePair_support_invariant hRS (fun t => Real.sinh (t/2))
    (sinh_memLp R) (sinh_memLp S) F G hF hG
  change archPair F G + boundedPart R C N F G = archPair F G + boundedPart S C N F G
  rw [boundedPart_apply, boundedPart_apply]
  change _ + (-C * spatialPair F G + 2 * profilePair R _ _ F G -
    2 * profilePair R _ _ F G - _) = _ +
    (-C * spatialPair F G + 2 * profilePair S _ _ F G - 2 * profilePair S _ _ F G - _)
  rw [hc, hs]

/-- An exact zero diagonal at the old radius remains EXACTLY zero under
literal support inclusion. This does not apply to a dilated old vector. -/
theorem old_null_diagonal_stays_zero {R S : ℝ} (hRS : R ≤ S)
    (C : ℝ) (N : ℕ) (p : FlatCoreSpace R)
    (hp : completeForm R C N (p : WeightedSpace) (p : WeightedSpace) = 0) :
    completeForm S C N (p : WeightedSpace) (p : WeightedSpace) = 0 := by
  rw [← completeForm_support_invariant hRS C N (p : WeightedSpace) (p : WeightedSpace)
    (flatCore_supported R p.property) (flatCore_supported R p.property)]
  exact hp

end RhLiteralSupportForm
#print axioms RhLiteralSupportForm.flatCore_mono
#print axioms RhLiteralSupportForm.profileMoment_support_invariant
#print axioms RhLiteralSupportForm.completeForm_support_invariant
#print axioms RhLiteralSupportForm.old_null_diagonal_stays_zero
