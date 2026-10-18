import RhNativeTranslationAlgebra001

/-! Actual signed rank-pair translation, and the complete finite native form.
Every profile change uses the physical L2 representatives and a full-line
change of variable; the source and translated supports are explicit.
-/
set_option maxHeartbeats 150000
set_option synthInstance.maxHeartbeats 20000
noncomputable section
open Set MeasureTheory Filter
open scoped Topology BigOperators
namespace RhNativeTranslationForm
open RhAnchored RhWeightedMeasureEmbedding RhNativeCompleteBilinear
open RhNativeCompleteDictionary RhWeightedTranslation RhNativeTranslationAlgebra

lemma profile_integrand_ae {R : ℝ} (f : ℝ → ℝ)
    (hf : MemLp f 2 (physicalMeasure R)) (F : WeightedSpace)
    (hF : F ∈ supportedSubspace R) :
    (fun t => inner ℂ (RhTail.physicalFourierVector R f hf t) (physicalEmbedding F t))
      =ᵐ[volume] (fun t => (f t : ℂ) * physicalEmbedding F t) := by
  have hp : RhTail.physicalFourierVector R f hf =ᵐ[volume] RhTail.complexExtension R f :=
    (RhTail.complexExtension_memLp hf).coeFn_toLp
  filter_upwards [hp, (mem_supportedSubspace_iff R F).mp hF] with t ht hs
  rw [ht]
  by_cases hi : t ∈ interval R
  · simp [RhTail.complexExtension, zeroExtension, hi, RCLike.inner_apply, mul_comm]
  · rw [hs hi]
    simp

lemma profile_product_integrable {R : ℝ} (f : ℝ → ℝ)
    (hf : MemLp f 2 (physicalMeasure R)) (F : WeightedSpace)
    (hF : F ∈ supportedSubspace R) :
    Integrable (fun t => (f t : ℂ) * physicalEmbedding F t) volume :=
  (L2.integrable_inner (𝕜 := ℂ) (RhTail.physicalFourierVector R f hf)
    (physicalEmbedding F)).congr (profile_integrand_ae f hf F hF)

lemma profileMoment_integral {R : ℝ} (f : ℝ → ℝ)
    (hf : MemLp f 2 (physicalMeasure R)) (F : WeightedSpace)
    (hF : F ∈ supportedSubspace R) :
    profileMoment R f hf F = ∫ t, (f t : ℂ) * physicalEmbedding F t := by
  change inner ℂ (RhTail.physicalFourierVector R f hf) (physicalEmbedding F) = _
  rw [L2.inner_def]
  exact integral_congr_ae (profile_integrand_ae f hf F hF)

/-- The actual profile is shifted by MINUS a under tau_a F(t)=F(t+a). -/
lemma profileMoment_translated_integral {S : ℝ} (f : ℝ → ℝ)
    (hf : MemLp f 2 (physicalMeasure S)) (F : WeightedSpace)
    (hF : Integrable (physicalEmbedding F) volume) (a : ℝ)
    (hT : translated F hF a ∈ supportedSubspace S) :
    profileMoment S f hf (translated F hF a) =
      ∫ t, (f (t-a) : ℂ) * physicalEmbedding F t := by
  rw [profileMoment_integral f hf _ hT]
  calc
    _ = ∫ t, (f t : ℂ) * physicalEmbedding F (t+a) := by
      apply integral_congr_ae
      filter_upwards [translated_physical_ae F hF a] with t ht
      rw [ht]
    _ = _ := by
      simpa only [add_sub_cancel_right] using
        integral_add_right_eq_self (fun t : ℝ => (f (t-a) : ℂ) * physicalEmbedding F t) a

lemma coshMoment_translated {R S : ℝ} (F : WeightedSpace)
    (hFR : F ∈ supportedSubspace R)
    (hF : Integrable (physicalEmbedding F) volume) (a : ℝ)
    (hT : translated F hF a ∈ supportedSubspace S) :
    profileMoment S (fun t => Real.cosh (t/2)) (cosh_memLp S) (translated F hF a) =
      Real.cosh (a/2) • profileMoment R (fun t => Real.cosh (t/2)) (cosh_memLp R) F -
      Real.sinh (a/2) • profileMoment R (fun t => Real.sinh (t/2)) (sinh_memLp R) F := by
  rw [profileMoment_translated_integral _ _ F hF a hT]
  have hc := profile_product_integrable (fun t => Real.cosh (t/2)) (cosh_memLp R) F hFR
  have hs := profile_product_integrable (fun t => Real.sinh (t/2)) (sinh_memLp R) F hFR
  have he (t : ℝ) : ((Real.cosh ((t-a)/2) : ℝ) : ℂ) * physicalEmbedding F t =
      (Real.cosh (a/2) : ℂ) * ((Real.cosh (t/2) : ℂ) * physicalEmbedding F t) -
      (Real.sinh (a/2) : ℂ) * ((Real.sinh (t/2) : ℂ) * physicalEmbedding F t) := by
    rw [show (t-a)/2 = t/2-a/2 by ring, Real.cosh_sub]
    simp only [Complex.ofReal_sub, Complex.ofReal_mul, Complex.real_smul]
    ring
  simp_rw [he]
  simp only [Complex.real_smul]
  rw [integral_sub (hc.const_mul (Real.cosh (a/2) : ℂ))
    (hs.const_mul (Real.sinh (a/2) : ℂ)), integral_const_mul, integral_const_mul,
    ← profileMoment_integral _ (cosh_memLp R) F hFR,
    ← profileMoment_integral _ (sinh_memLp R) F hFR]

lemma sinhMoment_translated {R S : ℝ} (F : WeightedSpace)
    (hFR : F ∈ supportedSubspace R)
    (hF : Integrable (physicalEmbedding F) volume) (a : ℝ)
    (hT : translated F hF a ∈ supportedSubspace S) :
    profileMoment S (fun t => Real.sinh (t/2)) (sinh_memLp S) (translated F hF a) =
      Real.cosh (a/2) • profileMoment R (fun t => Real.sinh (t/2)) (sinh_memLp R) F -
      Real.sinh (a/2) • profileMoment R (fun t => Real.cosh (t/2)) (cosh_memLp R) F := by
  rw [profileMoment_translated_integral _ _ F hF a hT]
  have hc := profile_product_integrable (fun t => Real.cosh (t/2)) (cosh_memLp R) F hFR
  have hs := profile_product_integrable (fun t => Real.sinh (t/2)) (sinh_memLp R) F hFR
  have he (t : ℝ) : ((Real.sinh ((t-a)/2) : ℝ) : ℂ) * physicalEmbedding F t =
      (Real.cosh (a/2) : ℂ) * ((Real.sinh (t/2) : ℂ) * physicalEmbedding F t) -
      (Real.sinh (a/2) : ℂ) * ((Real.cosh (t/2) : ℂ) * physicalEmbedding F t) := by
    rw [show (t-a)/2 = t/2-a/2 by ring, Real.sinh_sub]
    simp only [Complex.ofReal_sub, Complex.ofReal_mul, Complex.real_smul]
    ring
  simp_rw [he]
  simp only [Complex.real_smul]
  rw [integral_sub (hs.const_mul (Real.cosh (a/2) : ℂ))
    (hc.const_mul (Real.sinh (a/2) : ℂ)), integral_const_mul, integral_const_mul,
    ← profileMoment_integral _ (sinh_memLp R) F hFR,
    ← profileMoment_integral _ (cosh_memLp R) F hFR]

/-- Both native rank terms are required; neither is invariant separately. -/
theorem signed_rank_joint {R S : ℝ} (F G : WeightedSpace)
    (hFR : F ∈ supportedSubspace R) (hGR : G ∈ supportedSubspace R)
    (hF : Integrable (physicalEmbedding F) volume)
    (hG : Integrable (physicalEmbedding G) volume) (a : ℝ)
    (hTF : translated F hF a ∈ supportedSubspace S)
    (hTG : translated G hG a ∈ supportedSubspace S) :
    2*coshPair S (translated F hF a) (translated G hG a) -
      2*sinhPair S (translated F hF a) (translated G hG a) =
    2*coshPair R F G - 2*sinhPair R F G := by
  change 2 * inner ℝ (profileMoment S _ _ _) (profileMoment S _ _ _) -
      2 * inner ℝ (profileMoment S _ _ _) (profileMoment S _ _ _) =
    2 * inner ℝ (profileMoment R _ _ F) (profileMoment R _ _ G) -
      2 * inner ℝ (profileMoment R _ _ F) (profileMoment R _ _ G)
  rw [coshMoment_translated F hFR hF a hTF, coshMoment_translated G hGR hG a hTG,
    sinhMoment_translated F hFR hF a hTF, sinhMoment_translated G hGR hG a hTG]
  simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right]
  have hcs := Real.cosh_sq_sub_sinh_sq (a/2)
  calc
    _ = (Real.cosh (a/2)^2 - Real.sinh (a/2)^2) *
        (2 * inner ℝ (profileMoment R (fun t => Real.cosh (t/2)) (cosh_memLp R) F)
          (profileMoment R (fun t => Real.cosh (t/2)) (cosh_memLp R) G) -
        2 * inner ℝ (profileMoment R (fun t => Real.sinh (t/2)) (sinh_memLp R) F)
          (profileMoment R (fun t => Real.sinh (t/2)) (sinh_memLp R) G)) := by ring
    _ = _ := by rw [hcs, one_mul]

/-- One exact finite cap N; complete arch energy, scalar, BOTH ranks and both
translations for EVERY prescribed prime-power coefficient stay attached. -/
theorem completeForm_joint {R S : ℝ} (C : ℝ) (N : ℕ) (F G : WeightedSpace)
    (hFR : F ∈ supportedSubspace R) (hGR : G ∈ supportedSubspace R)
    (hF : Integrable (physicalEmbedding F) volume)
    (hG : Integrable (physicalEmbedding G) volume) (a : ℝ)
    (hTF : translated F hF a ∈ supportedSubspace S)
    (hTG : translated G hG a ∈ supportedSubspace S) :
    completeForm S C N (translated F hF a) (translated G hG a) =
      completeForm R C N F G := by
  change archPair _ _ + boundedPart S C N _ _ = archPair F G + boundedPart R C N F G
  rw [archPair_joint, boundedPart_apply, boundedPart_apply, spatialPair_joint]
  simp_rw [shiftPair_joint]
  have hk := signed_rank_joint F G hFR hGR hF hG a hTF hTG
  linarith

end RhNativeTranslationForm
#print axioms RhNativeTranslationForm.profileMoment_integral
#print axioms RhNativeTranslationForm.profileMoment_translated_integral
#print axioms RhNativeTranslationForm.coshMoment_translated
#print axioms RhNativeTranslationForm.sinhMoment_translated
#print axioms RhNativeTranslationForm.signed_rank_joint
#print axioms RhNativeTranslationForm.completeForm_joint
