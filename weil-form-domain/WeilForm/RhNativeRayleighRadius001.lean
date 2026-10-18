import RhNativeRayleighControl001
import RhLiteralSupportForm001

/-! Literal physical-primitive Rayleigh comparison across radii.
Every statement uses one exact common finite prime horizon. Continuity and
support monotonicity do not establish the sign of the Rayleigh bottom. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace RhNativeRayleighRadius
open RhWeightedMeasureEmbedding RhFlatSmoothCore RhNativeCompleteBilinear
open RhNativeRayleighDomain RhNativeRayleighControl RhFlatCoreDilation

lemma outward_physical_norm {R r : ℝ} (hr : 1 ≤ r) (F : FlatCoreSpace R) :
    ‖physicalEmbedding (outwardMap hr F : WeightedSpace)‖ =
      ‖physicalEmbedding (F : WeightedSpace)‖ := by
  have h := RhNativeDilationSmallness.scalar_mass_invariant hr F
  rw [spatialPair_apply, spatialPair_apply, real_inner_self_eq_norm_sq,
    real_inner_self_eq_norm_sq] at h
  nlinarith [norm_nonneg (physicalEmbedding (outwardMap hr F : WeightedSpace)),
    norm_nonneg (physicalEmbedding (F : WeightedSpace))]

lemma return_physical_norm {R r : ℝ} (hr : 1 ≤ r) (F : FlatCoreSpace (r*R)) :
    ‖physicalEmbedding (returnMap hr F : WeightedSpace)‖ =
      ‖physicalEmbedding (F : WeightedSpace)‖ := by
  have h := outward_physical_norm hr (returnMap hr F)
  rw [outward_return_cancel] at h
  exact h.symm

/-- Exact equality of the genuine Rayleigh sets, not merely an upper estimate. -/
theorem pulledBottom_eq_bottom {R r : ℝ} (hr : 1 ≤ r) (C : ℝ) (N : ℕ) :
    pulledBottom (R:=R) hr C N = bottom (r*R) C N := by
  unfold pulledBottom bottom RhVariationalInfimum.ground
  congr 1
  ext y
  constructor
  · rintro ⟨F,hF,rfl⟩
    refine ⟨outwardMap hr F, ?_, rfl⟩
    change ‖physicalEmbedding (outwardMap hr F : WeightedSpace)‖ = 1
    rw [outward_physical_norm]
    exact hF
  · rintro ⟨F,hF,rfl⟩
    refine ⟨returnMap hr F, ?_, ?_⟩
    · change ‖physicalEmbedding (returnMap hr F : WeightedSpace)‖ = 1
      rw [return_physical_norm]
      exact hF
    · change RhPulledCompleteForm.baseForm (r*R) C N
        (outwardMap hr (returnMap hr F)) (outwardMap hr (returnMap hr F)) = _
      rw [outward_return_cancel]
      rfl

/-- Native right continuity in the actual enlarged radius, not a surrogate form. -/
theorem right_continuity {R : ℝ} (hR : 0 < R) (C : ℝ) (N : ℕ)
    {eps : ℝ} (heps : 0 < eps) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ (r : ℝ) (hr : 1 ≤ r), |r-1| < delta →
      |bottom (r*R) C N-bottom R C N| < eps := by
  obtain ⟨delta,hd,hc⟩ := local_ground_continuity hR C N heps
  refine ⟨delta,hd,?_⟩
  intro r hr hh
  rw [←pulledBottom_eq_bottom hr]
  exact hc r hr hh

/-- Increasing support can only lower the literal primitive Rayleigh infimum.
This monotonicity does NOT propagate a local nonnegative lower bound outward. -/
theorem bottom_antitone_support {R S : ℝ} (hR : 0 < R) (hRS : R ≤ S)
    (C : ℝ) (N : ℕ) : bottom S C N ≤ bottom R C N := by
  apply le_csInf ((physicalUnit_nonempty hR).image (diagonal R C N))
  rintro y ⟨F,hF,rfl⟩
  let G : FlatCoreSpace S := ⟨(F : WeightedSpace),
    RhLiteralSupportForm.flatCore_mono hRS F.property⟩
  have hG : G ∈ physicalUnit S := hF
  have hh := bottom_le_diagonal S C N G hG
  have he : diagonal R C N F = diagonal S C N G :=
    RhLiteralSupportForm.completeForm_support_invariant hRS C N F F
      (flatCore_supported R F.property) (flatCore_supported R F.property)
  rw [he]
  exact hh

end RhNativeRayleighRadius
#print axioms RhNativeRayleighRadius.pulledBottom_eq_bottom
#print axioms RhNativeRayleighRadius.right_continuity
#print axioms RhNativeRayleighRadius.bottom_antitone_support
