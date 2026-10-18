import RhSupportedMollifier001

/-! Real-valued actual spatial mollification. The complete weighted error is
the SAME already-certified mollifier error; reality is recovered by choosing
an actual pointwise-real compact representative, not by an unproved weighted
projection onto real parts. -/
set_option maxHeartbeats 0
noncomputable section
open Set MeasureTheory Filter FourierTransform
open scoped Topology ContDiff Convolution
namespace RhRealMollifier
open RhWeightedMeasureEmbedding RhWeightedEnergyIdentity RhWeightedMollifier
open RhScaledMollifier RhSpatialMollifier RhWeightedCoreAttempt

def IsPhysicalReal (F : WeightedSpace) : Prop :=
  ∀ᵐ t ∂volume, (physicalEmbedding F t).im = 0

def realRepresentative (R : ℝ) (F : SupportedSpace R) : ℝ → ℝ :=
  (Icc (-R) R).indicator (fun t => (physicalEmbedding (F : WeightedSpace) t).re)

lemma realRepresentative_complex_ae {R : ℝ} (F : SupportedSpace R)
    (hreal : IsPhysicalReal (F : WeightedSpace)) :
    (fun t => (realRepresentative R F t : ℂ)) =ᵐ[volume]
      physicalEmbedding (F : WeightedSpace) := by
  filter_upwards [hreal, (mem_supportedSubspace_iff R (F : WeightedSpace)).mp F.property]
    with t ht hs
  by_cases hin : t ∈ Icc (-R) R
  · simp only [realRepresentative, indicator_of_mem hin]
    apply Complex.ext
    · simp
    · simpa only [Complex.ofReal_im] using ht.symm
  · simp [realRepresentative, hin, hs hin]

lemma realRepresentative_memLp {R : ℝ} (F : SupportedSpace R) :
    MemLp (realRepresentative R F) 2 volume := by
  have h : MemLp (fun t => (physicalEmbedding (F : WeightedSpace) t).re) 2 volume := by
    simpa only [RCLike.re_eq_complex_re] using (Lp.memLp (physicalEmbedding (F : WeightedSpace))).re
  exact h.indicator measurableSet_Icc.nullMeasurableSet

lemma realRepresentative_integrable {R : ℝ} (F : SupportedSpace R) :
    Integrable (realRepresentative R F) volume := by
  have h : Integrable (fun t => (physicalEmbedding (F : WeightedSpace) t).re) volume := by
    simpa only [RCLike.re_eq_complex_re] using
      (RhPhysicalShiftFourier.supported_integrable F.property).re
  exact h.indicator measurableSet_Icc

lemma realRepresentative_support {R : ℝ} (F : SupportedSpace R) :
    Function.support (fun t => (realRepresentative R F t : ℂ)) ⊆ Icc (-R) R := by
  intro t ht
  by_contra hn
  exact ht (by simp [realRepresentative, hn])

lemma realRepresentative_complex_compact {R : ℝ} (F : SupportedSpace R) :
    HasCompactSupport (fun t => (realRepresentative R F t : ℂ)) :=
  HasCompactSupport.of_support_subset_isCompact isCompact_Icc (realRepresentative_support F)

/-- Exact ordinary real convolution underlying the same complex mollifier. -/
def realMollification (phi : ContDiffBump (0 : ℝ)) (n : ℕ)
    (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ s, (scale n * phi.normed volume (scale n * s)) * f (t - s)

lemma mollification_ofReal (phi : ContDiffBump (0 : ℝ)) (n : ℕ)
    (f : ℝ → ℝ) (t : ℝ) :
    mollification phi n (fun x => (f x : ℂ)) t = (realMollification phi n f t : ℂ) := by
  change (∫ s, scaledBump phi n s * (f (t - s) : ℂ)) = _
  simp only [scaledBump, bumpComplex, ← Complex.ofReal_mul, integral_complex_ofReal,
    realMollification]

lemma realMollification_contDiff (phi : ContDiffBump (0 : ℝ)) (n : ℕ)
    {f : ℝ → ℝ} (hf : Integrable f volume) :
    ContDiff ℝ ∞ (realMollification phi n f) := by
  have he : realMollification phi n f = fun t =>
      (mollification phi n (fun x => (f x : ℂ)) t).re := by
    funext t
    rw [mollification_ofReal]
    simp
  rw [he]
  exact Complex.reCLM.contDiff.comp (mollification_contDiff phi n hf.ofReal)

lemma realMollification_tsupport (phi : ContDiffBump (0 : ℝ)) (n : ℕ) (f : ℝ → ℝ) :
    tsupport (realMollification phi n f) =
      tsupport (mollification phi n (fun x => (f x : ℂ))) := by
  apply congrArg closure
  ext t
  simp only [Function.mem_support, mollification_ofReal, ne_eq, Complex.ofReal_eq_zero]

/-- Real smooth approximation across a declared gap, in the COMPLETE native
weighted norm, with an actual physical real representative at every finite stage. -/
theorem exists_real_smooth_across_gap (phi : ContDiffBump (0 : ℝ))
    {R S eps : ℝ} (hRS : R < S) (heps : 0 < eps) (F : SupportedSpace R)
    (hreal : IsPhysicalReal (F : WeightedSpace)) :
    ∃ (f : ℝ → ℝ) (X : SupportedSpace S),
      ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧ tsupport f ⊆ Ioo (-S) S ∧
      physicalEmbedding (X : WeightedSpace) =ᵐ[volume] (fun t => (f t : ℂ)) ∧
      ‖(X : WeightedSpace) - (F : WeightedSpace)‖ < eps := by
  have herr : ∀ᶠ n in atTop, ‖mollified phi n (F : WeightedSpace) - (F : WeightedSpace)‖ < eps :=
    (mollified_norm_tendsto phi (F : WeightedSpace)).eventually (eventually_lt_nhds heps)
  have hrad : Tendsto (fun n => R + phi.rOut / scale n) atTop (𝓝 R) := by
    simpa only [add_zero] using (RhSupportedMollifier.mollifier_radius_tendsto phi).const_add R
  have hgap : ∀ᶠ n in atTop, R + phi.rOut / scale n < S :=
    hrad.eventually (eventually_lt_nhds hRS)
  obtain ⟨n, hn, hngap⟩ := (herr.and hgap).exists
  let f := realMollification phi n (realRepresentative R F)
  have hfS : ContDiff ℝ ∞ f := realMollification_contDiff phi n (realRepresentative_integrable F)
  have hrep2 : MemLp (fun t => (realRepresentative R F t : ℂ)) 2 volume :=
    (realRepresentative_memLp F).ofReal
  have hrep1 : Integrable (fun t => (realRepresentative R F t : ℂ)) volume :=
    (realRepresentative_integrable F).ofReal
  have hrep : physicalEmbedding (F : WeightedSpace) =
      hrep2.toLp (fun t => (realRepresentative R F t : ℂ)) := by
    apply Lp.ext
    exact (realRepresentative_complex_ae F hreal).symm.trans hrep2.coeFn_toLp.symm
  have hfT : tsupport f ⊆ Ioo (-S) S := by
    rw [realMollification_tsupport]
    intro t ht
    have hb := mollification_tsupport phi n (realRepresentative_support F) ht
    constructor <;> linarith [hb.1, hb.2]
  have hfC : HasCompactSupport f := by
    change IsCompact (tsupport f)
    rw [realMollification_tsupport]
    exact mollification_hasCompactSupport phi n (realRepresentative_complex_compact F)
  have ha : physicalEmbedding (mollified phi n (F : WeightedSpace)) =ᵐ[volume]
      fun t => (f t : ℂ) := by
    rw [mollification_physical phi n (F : WeightedSpace) hrep1
      (realRepresentative_complex_compact F) hrep2 hrep]
    have h := (mollification_memLp phi n hrep1 (realRepresentative_complex_compact F)).coeFn_toLp
    filter_upwards [h] with t ht
    rw [ht, mollification_ofReal]
  have hm : mollified phi n (F : WeightedSpace) ∈ supportedSubspace S := by
    apply (mem_supportedSubspace_iff S _).mpr
    filter_upwards [ha] with t ht
    intro hout
    rw [ht]
    have hf0 : f t = 0 := by
      by_contra hnz
      have hin := hfT (subset_tsupport f hnz)
      exact hout ⟨hin.1.le, hin.2.le⟩
    simp only [hf0, Complex.ofReal_zero]
  exact ⟨f, ⟨mollified phi n (F : WeightedSpace), hm⟩, hfS, hfC, hfT, ha, hn⟩

end RhRealMollifier
#print axioms RhRealMollifier.realRepresentative_complex_ae
#print axioms RhRealMollifier.mollification_ofReal
#print axioms RhRealMollifier.exists_real_smooth_across_gap
