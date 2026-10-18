import RhNativeRayleighPositivity001
import RhInwardOldNullLift001

/-! Left continuity of the native primitive Rayleigh bottom. The proof uses
actual same-window strong inward transport, exact physical mass, and literal
support invariance. No arithmetic residual sign is assumed. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace RhNativeRayleighLeft
open RhWeightedMeasureEmbedding RhFlatSmoothCore RhNativeCompleteBilinear
open RhNativeRayleighDomain RhNativeRayleighRadius RhFlatCoreDilation
open RhSupportedInwardStrong

lemma inward_physical_norm {R r : ℝ} (hr : 1 ≤ r) (F : FlatCoreSpace R) :
    ‖physicalEmbedding (inwardMap hr F : WeightedSpace)‖ =
      ‖physicalEmbedding (F : WeightedSpace)‖ := by
  have h := outward_physical_norm hr (inwardMap hr F)
  change ‖physicalEmbedding (outwardMap hr (inwardMap hr F) : WeightedSpace)‖ = _ at h
  rw [outward_inward_cancel] at h
  exact h.symm

/-- Every near-minimizing actual vector has an inward, physically normalized
counterpart on some strictly smaller radius with nearly identical energy. -/
theorem near_minimum_on_smaller_radius {R : ℝ} (hR : 0 < R) (C : ℝ) (N : ℕ)
    {eps : ℝ} (heps : 0 < eps) :
    ∃ S : ℝ, 0 < S ∧ S < R ∧ bottom S C N < bottom R C N+eps := by
  have he2 : 0 < eps/2 := by positivity
  obtain ⟨y,hy,hyl⟩ := exists_lt_of_csInf_lt
    ((physicalUnit_nonempty hR).image (diagonal R C N))
    (by change bottom R C N < bottom R C N+eps/2; linarith)
  obtain ⟨F,hF,rfl⟩ := hy
  let X (n : ℕ) : FlatCoreSpace (inwardRadius R n) :=
    inwardMap (inwardScale_ge_one n) F
  have hnorm : Tendsto (fun n => ‖(X n : WeightedSpace)-(F : WeightedSpace)‖)
      atTop (𝓝 0) := by
    let Y : SupportedSpace R := ⟨(F : WeightedSpace),flatCore_supported R F.property⟩
    exact canonical_supported_inward_norm_tendsto Y
  have ht : Tendsto (fun n => (X n : WeightedSpace)) atTop (𝓝 (F : WeightedSpace)) :=
    tendsto_iff_norm_sub_tendsto_zero.mpr hnorm
  have hcont : Continuous (fun Z : WeightedSpace => completeForm R C N Z Z) :=
    (completeForm R C N).continuous.clm_apply continuous_id
  have htq := hcont.continuousAt.tendsto.comp ht
  have htarget : completeForm R C N (F : WeightedSpace) (F : WeightedSpace) <
      bottom R C N+eps := by change diagonal R C N F < _; linarith
  obtain ⟨n,hn⟩ := (htq.eventually (eventually_lt_nhds htarget)).exists
  let S := inwardRadius R n
  have hS := inwardRadius_pos_lt hR n
  have hu : X n ∈ physicalUnit S := by
    change ‖physicalEmbedding (inwardMap (inwardScale_ge_one n) F : WeightedSpace)‖ = 1
    rw [inward_physical_norm]
    exact hF
  have he : diagonal S C N (X n) =
      completeForm R C N (X n : WeightedSpace) (X n : WeightedSpace) :=
    RhLiteralSupportForm.completeForm_support_invariant hS.2.le C N (X n) (X n)
      (flatCore_supported S (X n).property) (flatCore_supported S (X n).property)
  refine ⟨S,hS.1,hS.2,?_⟩
  exact (bottom_le_diagonal S C N (X n) hu).trans_lt (he ▸ hn)

/-- Uniform left-radius neighborhood, obtained from a single strict-interior
near-minimizer and exact support monotonicity. -/
theorem left_continuity {R : ℝ} (hR : 0 < R) (C : ℝ) (N : ℕ)
    {eps : ℝ} (heps : 0 < eps) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ S : ℝ, R-delta < S → S ≤ R →
      |bottom S C N-bottom R C N| < eps := by
  obtain ⟨T,hT,hTR,hb⟩ := near_minimum_on_smaller_radius hR C N heps
  refine ⟨R-T,sub_pos.mpr hTR,?_⟩
  intro S hS hSR
  have hTS : T < S := by linarith
  have hlo := bottom_antitone_support (hT.trans hTS) hSR C N
  have hhi := bottom_antitone_support hT hTS.le C N
  rw [abs_of_nonneg (sub_nonneg.mpr hlo)]
  linarith

end RhNativeRayleighLeft
#print axioms RhNativeRayleighLeft.near_minimum_on_smaller_radius
#print axioms RhNativeRayleighLeft.left_continuity
