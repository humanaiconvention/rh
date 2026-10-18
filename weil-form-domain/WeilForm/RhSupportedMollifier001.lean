import RhSpatialMollifier001

/-! Actual compact representatives and smooth approximation across an explicit
support gap. This is a weighted graph-norm theorem, not plain L2 density.
It does not assert a same-support theorem for arbitrary graph-domain vectors.
-/
noncomputable section
open Set MeasureTheory Filter FourierTransform
open scoped Topology ContDiff
namespace RhSupportedMollifier
open RhWeightedMeasureEmbedding RhWeightedEnergyIdentity RhWeightedCoreAttempt
open RhWeightedMollifier RhScaledMollifier RhSpatialMollifier

def representative (R : ℝ) (F : SupportedSpace R) : ℝ → ℂ :=
  (Icc (-R) R).indicator (physicalEmbedding (F : WeightedSpace))

lemma representative_ae {R : ℝ} (F : SupportedSpace R) :
    representative R F =ᵐ[volume] physicalEmbedding (F : WeightedSpace) := by
  filter_upwards [(mem_supportedSubspace_iff R (F : WeightedSpace)).mp F.property] with t ht
  by_cases h : t ∈ Icc (-R) R
  · simp only [representative, indicator_of_mem h]
  · simp [representative, h, ht h]

lemma representative_memLp {R : ℝ} (F : SupportedSpace R) :
    MemLp (representative R F) 2 volume :=
  (Lp.memLp (physicalEmbedding (F : WeightedSpace))).indicator measurableSet_Icc.nullMeasurableSet

lemma representative_integrable {R : ℝ} (F : SupportedSpace R) :
    Integrable (representative R F) volume :=
  (RhPhysicalShiftFourier.supported_integrable F.property).indicator measurableSet_Icc

lemma representative_support {R : ℝ} (F : SupportedSpace R) :
    Function.support (representative R F) ⊆ Icc (-R) R := by
  intro t ht
  by_contra hn
  exact ht (by simp [representative, hn])

lemma representative_compact {R : ℝ} (F : SupportedSpace R) :
    HasCompactSupport (representative R F) :=
  HasCompactSupport.of_support_subset_isCompact isCompact_Icc (representative_support F)

lemma representative_toLp {R : ℝ} (F : SupportedSpace R) :
    physicalEmbedding (F : WeightedSpace) =
      (representative_memLp F).toLp (representative R F) := by
  apply Lp.ext
  exact (representative_ae F).symm.trans (representative_memLp F).coeFn_toLp.symm

lemma mollifier_physical_ae (phi : ContDiffBump (0 : ℝ)) (n : ℕ)
    {R : ℝ} (F : SupportedSpace R) :
    physicalEmbedding (mollified phi n (F : WeightedSpace)) =ᵐ[volume]
      mollification phi n (representative R F) := by
  rw [mollification_physical phi n (F : WeightedSpace)
    (representative_integrable F) (representative_compact F) (representative_memLp F)
    (representative_toLp F)]
  exact (mollification_memLp phi n (representative_integrable F)
    (representative_compact F)).coeFn_toLp

lemma mollifier_radius_tendsto (phi : ContDiffBump (0 : ℝ)) :
    Tendsto (fun n => phi.rOut / scale n) atTop (𝓝 0) := by
  have hs : Tendsto (fun n => scale n) atTop atTop := by
    simpa only [scale, add_comm] using
      tendsto_atTop_add_const_left atTop (1 : ℝ)
        (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)
  simpa only [Function.comp_def, div_eq_mul_inv, mul_zero] using
    (tendsto_inv_atTop_zero.comp hs).const_mul phi.rOut

/-- Any fixed positive support gap admits actual compact smooth approximation
in the full native graph norm, for every prescribed error tolerance. -/
theorem exists_smooth_across_gap (phi : ContDiffBump (0 : ℝ))
    {R S eps : ℝ} (hRS : R < S) (heps : 0 < eps) (F : SupportedSpace R) :
    ∃ (f : ℝ → ℂ) (X : SupportedSpace S),
      ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧ tsupport f ⊆ Ioo (-S) S ∧
      physicalEmbedding (X : WeightedSpace) =ᵐ[volume] f ∧
      ‖(X : WeightedSpace) - (F : WeightedSpace)‖ < eps := by
  have herr : ∀ᶠ n in atTop, ‖mollified phi n (F : WeightedSpace) - (F : WeightedSpace)‖ < eps :=
    (mollified_norm_tendsto phi (F : WeightedSpace)).eventually (eventually_lt_nhds heps)
  have hrad : Tendsto (fun n => R + phi.rOut / scale n) atTop (𝓝 R) := by
    simpa only [add_zero] using (mollifier_radius_tendsto phi).const_add R
  have hgap : ∀ᶠ n in atTop, R + phi.rOut / scale n < S :=
    hrad.eventually (eventually_lt_nhds hRS)
  obtain ⟨n, hn, hngap⟩ := (herr.and hgap).exists
  let f := mollification phi n (representative R F)
  have hfS : ContDiff ℝ ∞ f := mollification_contDiff phi n (representative_integrable F)
  have hfC : HasCompactSupport f := mollification_hasCompactSupport phi n (representative_compact F)
  have hfT : tsupport f ⊆ Ioo (-S) S := by
    intro t ht
    have hb := mollification_tsupport phi n (representative_support F) ht
    constructor <;> linarith [hb.1, hb.2]
  have ha := mollifier_physical_ae phi n F
  have hm : mollified phi n (F : WeightedSpace) ∈ supportedSubspace S := by
    apply (mem_supportedSubspace_iff S _).mpr
    filter_upwards [ha] with t ht
    intro hnot
    rw [ht]
    by_contra hnz
    have hinside := hfT (subset_tsupport f hnz)
    exact hnot ⟨hinside.1.le, hinside.2.le⟩
  refine ⟨f, ⟨mollified phi n (F : WeightedSpace), hm⟩, hfS, hfC, hfT, ha, hn⟩

end RhSupportedMollifier
#print axioms RhSupportedMollifier.mollifier_physical_ae
#print axioms RhSupportedMollifier.exists_smooth_across_gap
