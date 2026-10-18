import RhSmoothJetProfiles001
import RhSmoothDerivativeDictionary001

/-! Actual complete-domain lifts of the literal smooth jet profiles. Every
physical identification is AE; derivatives are taken only of the named smooth
representative. -/
noncomputable section
set_option maxHeartbeats 150000
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace RhSmoothJetLifts
open RhSmoothJetProfiles RhWeightedMeasureEmbedding RhWeightedPrimitiveLift
open RhSmoothDerivativeDictionary RhTranslatedJetCapacity RhTranslatedJetDictionary RhAnchored

def radius (chi : ContDiffBump (0 : ℝ)) : ℝ := chi.rOut + 1
lemma radius_pos (chi : ContDiffBump (0 : ℝ)) : 0 < radius chi := by
  unfold radius
  linarith [chi.rOut_pos]

lemma profile_tsupport (chi : ContDiffBump (0 : ℝ)) (j : ℕ) :
    tsupport (profile chi j) ⊆ Ioo (-radius chi) (radius chi) := by
  intro t ht
  have hh : t ∈ tsupport (chi : ℝ → ℝ) :=
    tsupport_mul_subset_right ht
  rw [chi.tsupport_eq, Metric.mem_closedBall, Real.dist_eq, sub_zero] at hh
  have hb := abs_le.mp hh
  constructor <;> unfold radius <;> linarith

/-- A real smooth function strictly supported in its window has a concrete
native weighted lift, constructed from its actual derivative. -/
def smoothLift {R : ℝ} (hR : 0 < R) (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) : WeightedSpace :=
  actualPrimitiveLift hR (deriv f) (derivative_memLp hf)

lemma smoothLift_physical {R : ℝ} (hR : 0 < R) (f : ℝ → ℝ)
    (hf : ContDiff ℝ ∞ f) (hs : tsupport f ⊆ Ioo (-R) R) :
    physicalEmbedding (smoothLift hR f hf) =ᵐ[volume] fun t => (f t : ℂ) := by
  rw [smoothLift, actualPrimitiveLift_physical]
  have hraw : RhTail.physicalFourierVector R (primitive R (deriv f))
      (primitive_memLp (derivative_memLp hf)) =ᵐ[volume]
      RhTail.complexExtension R (primitive R (deriv f)) :=
    (RhTail.complexExtension_memLp (primitive_memLp (derivative_memLp hf))).coeFn_toLp
  filter_upwards [hraw, primitive_derivative_ae hR hf hs] with t ht hp
  rw [ht]
  by_cases hi : t ∈ interval R
  · simp [RhTail.complexExtension, zeroExtension, hi, hp]
  · have hz : f t = 0 := by
      by_contra hn
      have hh := hs (subset_tsupport f hn)
      exact hi ⟨hh.1.le, hh.2.le⟩
    simp [RhTail.complexExtension, zeroExtension, hi, hz]

lemma smoothLift_supported {R : ℝ} (hR : 0 < R) (f : ℝ → ℝ)
    (hf : ContDiff ℝ ∞ f) : smoothLift hR f hf ∈ supportedSubspace R :=
  actualPrimitiveLift_supported hR _ _

def profileLift (chi : ContDiffBump (0 : ℝ)) (j : ℕ) : WeightedSpace :=
  smoothLift (radius_pos chi) (profile chi j) (profile_contDiff chi j)

lemma profileLift_supported (chi : ContDiffBump (0 : ℝ)) (j : ℕ) :
    profileLift chi j ∈ supportedSubspace (radius chi) := smoothLift_supported _ _ _

lemma profileLift_physical (chi : ContDiffBump (0 : ℝ)) (j : ℕ) :
    physicalEmbedding (profileLift chi j) =ᵐ[volume] fun t => (profile chi j t : ℂ) :=
  smoothLift_physical _ _ _ (profile_tsupport chi j)

def jetLift (chi : ContDiffBump (0 : ℝ)) (j : ℕ) (x : ℝ) (n : ℕ) : WeightedSpace :=
  jetVector j (profileLift chi j) (profileLift_supported chi j) x n

theorem jetLift_physical (chi : ContDiffBump (0 : ℝ)) (j : ℕ) (x : ℝ) (n : ℕ) :
    physicalEmbedding (jetLift chi j x n) =ᵐ[volume]
      fun t => (scaledProfile chi j (scale n) x t : ℂ) := by
  have h := jetVector_physical_ae j (profileLift chi j)
    (profileLift_supported chi j) x n (fun t => (profile chi j t : ℂ))
    (profileLift_physical chi j)
  filter_upwards [h] with t ht
  simpa only [jetLift, scaledProfile, Complex.ofReal_mul, Complex.ofReal_inv,
    Complex.ofReal_pow] using ht

theorem jetLift_norm_tendsto (chi : ContDiffBump (0 : ℝ)) (j : ℕ) (x : ℝ) :
    Tendsto (fun n => ‖jetLift chi j x n‖) atTop (𝓝 0) :=
  jetVector_norm_tendsto_zero j (profileLift chi j) (profileLift_supported chi j) x

/-- Each literal smooth scaled profile has compact support; no cutoff or
magnitude approximation is introduced. -/
lemma scaledProfile_compact (chi : ContDiffBump (0 : ℝ)) (j : ℕ)
    {r : ℝ} (hr : r ≠ 0) (x : ℝ) : HasCompactSupport (scaledProfile chi j r x) := by
  apply HasCompactSupport.of_support_subset_isCompact
    (isCompact_closedBall (x := x) (r := chi.rOut / |r|))
  intro t ht
  have hn : chi ((t-x)*r) ≠ 0 := by
    intro hz
    apply ht
    simp [scaledProfile, profile, hz]
  have hb : |(t-x)*r| < chi.rOut := by
    have hm : (t-x)*r ∈ Function.support (chi : ℝ → ℝ) := hn
    rw [chi.support_eq, Metric.mem_ball, Real.dist_eq, sub_zero] at hm
    exact hm
  rw [Metric.mem_closedBall, Real.dist_eq]
  apply le_of_lt
  apply (lt_div_iff₀ (abs_pos.mpr hr)).mpr
  simpa only [abs_mul] using hb

end RhSmoothJetLifts
#print axioms RhSmoothJetLifts.smoothLift_physical
#print axioms RhSmoothJetLifts.jetLift_physical
#print axioms RhSmoothJetLifts.jetLift_norm_tendsto
#print axioms RhSmoothJetLifts.scaledProfile_compact

