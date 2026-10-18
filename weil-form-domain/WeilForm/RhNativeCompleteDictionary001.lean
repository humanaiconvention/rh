import RhNativeCompleteBilinear001
import RhPhysicalShiftFourier001

/-!
Exact native physical identification of the constructed complete bounded
bilinear form. Every L2 representative substitution, including both shifted
arguments, is made only almost everywhere. No positivity is presumed.
-/
noncomputable section
open Set MeasureTheory Filter FourierTransform
open scoped Topology BigOperators ENNReal
namespace RhNativeCompleteDictionary
open RhAnchored RhWeightedMeasureEmbedding RhWeightedEnergyIdentity
open RhWeightedPrimitiveLift RhNativeCompleteBilinear

/-- Actual compact physical vectors retain their literal complex moments. -/
lemma physicalVector_inner {R : ℝ} {f w : ℝ → ℝ}
    (hf : MemLp f 2 (physicalMeasure R)) (hw : MemLp w 2 (physicalMeasure R)) :
    inner ℂ (RhTail.physicalFourierVector R f hf) (RhTail.physicalFourierVector R w hw) =
      ((∫ t in interval R, f t * w t : ℝ) : ℂ) := by
  rw [L2.inner_def]
  have hfe : RhTail.physicalFourierVector R f hf =ᵐ[volume] RhTail.complexExtension R f :=
    (RhTail.complexExtension_memLp hf).coeFn_toLp
  have hwe : RhTail.physicalFourierVector R w hw =ᵐ[volume] RhTail.complexExtension R w :=
    (RhTail.complexExtension_memLp hw).coeFn_toLp
  calc
    _ = ∫ t, (interval R).indicator (fun t => ((f t * w t : ℝ) : ℂ)) t := by
      apply integral_congr_ae
      filter_upwards [hfe, hwe] with t ht hu
      rw [ht, hu]
      by_cases hi : t ∈ interval R
      · simp [RhTail.complexExtension, zeroExtension, hi, RCLike.inner_apply, mul_comm]
      · simp [RhTail.complexExtension, zeroExtension, hi]
    _ = _ := by
      change (∫ t, (Icc (-R) R).indicator (fun t => ((f t * w t : ℝ) : ℂ)) t) = _
      rw [integral_indicator measurableSet_Icc, integral_complex_ofReal]
      rfl

lemma profileMoment_actual {R : ℝ} (hR : 0 < R) {v : ℝ → ℝ}
    (hv : MemLp v 2 (physicalMeasure R)) (f : ℝ → ℝ)
    (hf : MemLp f 2 (physicalMeasure R)) :
    profileMoment R f hf (actualPrimitiveLift hR v hv) =
      ((∫ t in interval R, f t * primitive R v t : ℝ) : ℂ) := by
  change inner ℂ (RhTail.physicalFourierVector R f hf)
    (physicalEmbedding (actualPrimitiveLift hR v hv)) = _
  rw [actualPrimitiveLift_physical]
  exact physicalVector_inner hf (primitive_memLp hv)

lemma profilePair_actual {R : ℝ} (hR : 0 < R) {v : ℝ → ℝ}
    (hv : MemLp v 2 (physicalMeasure R)) (f : ℝ → ℝ)
    (hf : MemLp f 2 (physicalMeasure R)) :
    profilePair R f hf (actualPrimitiveLift hR v hv) (actualPrimitiveLift hR v hv) =
      (∫ t in interval R, f t * primitive R v t)^2 := by
  rw [profilePair_diagonal, profileMoment_actual hR hv f hf]
  simp [Complex.norm_real, Real.norm_eq_abs, sq_abs]

lemma translation_ae (u : WholeSpace) (ell : ℝ) :
    translation ell u =ᵐ[volume] fun t => u (t + ell) :=
  Lp.coeFn_compMeasurePreserving u (measurePreserving_add_right volume ell)

lemma translation_inner (u v : WholeSpace) (ell : ℝ) :
    inner ℝ u (translation ell v) = ∫ t, inner ℝ (u t) (v (t + ell)) := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [translation_ae v ell] with t ht
  rw [ht]

/-- The actual two-translation CLM equals the literal spatial two-delay pairing. -/
theorem twoShift_spatial_dictionary (u v : WholeSpace) (ell : ℝ) :
    inner ℝ u (twoShift ell v) = RhPhysicalShiftFourier.spatialPair u v ell := by
  change inner ℝ u (translation ell v + translation (-ell) v) = _
  rw [inner_add_right, translation_inner, translation_inner]
  unfold RhPhysicalShiftFourier.spatialPair
  simp_rw [sub_eq_add_neg]
  rw [integral_add (RhPhysicalShiftFourier.shifted_integrable u v ell)
    (RhPhysicalShiftFourier.shifted_integrable u v (-ell))]

/-- Both translated representative changes are pulled back through actual
Lebesgue measure-preserving translations before the integral is changed. -/
lemma physicalVector_shift {R : ℝ} {w : ℝ → ℝ}
    (hw : MemLp w 2 (physicalMeasure R)) (ell : ℝ) :
    inner ℝ (RhTail.physicalFourierVector R w hw)
      (twoShift ell (RhTail.physicalFourierVector R w hw)) =
      ∫ t in interval R, primeShift R ell w t * w t := by
  rw [twoShift_spatial_dictionary, RhDilation.actual_shift_pairing]
  have he : RhTail.physicalFourierVector R w hw =ᵐ[volume] RhTail.complexExtension R w :=
    (RhTail.complexExtension_memLp hw).coeFn_toLp
  have hep := (measurePreserving_add_right volume ell).quasiMeasurePreserving.ae he
  have hem := (measurePreserving_add_right volume (-ell)).quasiMeasurePreserving.ae he
  unfold RhPhysicalShiftFourier.spatialPair RhDilation.realShift
  apply integral_congr_ae
  filter_upwards [he, hep, hem] with t ht hp hm
  change inner ℝ (RhTail.physicalFourierVector R w hw t)
      (RhTail.physicalFourierVector R w hw (t + ell)) +
    inner ℝ (RhTail.physicalFourierVector R w hw t)
      (RhTail.physicalFourierVector R w hw (t - ell)) = _
  rw [ht, hp, sub_eq_add_neg, hm]
  simp [RhTail.complexExtension, real_inner_eq_re_inner ℂ, RCLike.inner_apply,
    mul_comm, mul_add, add_mul]

lemma spatialPair_actual {R : ℝ} (hR : 0 < R) {v : ℝ → ℝ}
    (hv : MemLp v 2 (physicalMeasure R)) :
    spatialPair (actualPrimitiveLift hR v hv) (actualPrimitiveLift hR v hv) =
      ∫ t in interval R, (primitive R v t)^2 := by
  rw [spatialPair_apply, actualPrimitiveLift_physical, real_inner_self_eq_norm_sq]
  exact physicalVector_norm_square (primitive_memLp hv)

lemma shiftPair_actual {R : ℝ} (hR : 0 < R) {v : ℝ → ℝ}
    (hv : MemLp v 2 (physicalMeasure R)) (ell : ℝ) :
    shiftPair ell (actualPrimitiveLift hR v hv) (actualPrimitiveLift hR v hv) =
      ∫ t in interval R, primeShift R ell (primitive R v) t * primitive R v t := by
  rw [shiftPair_diagonal, actualPrimitiveLift_physical]
  exact physicalVector_shift (primitive_memLp hv) ell

/-- Exact full signed bounded perturbation on every actual real primitive. -/
theorem boundedPart_actual {R : ℝ} (hR : 0 < R) {v : ℝ → ℝ}
    (hv : MemLp v 2 (physicalMeasure R)) (C : ℝ) (N : ℕ) :
    boundedPart R C N (actualPrimitiveLift hR v hv) (actualPrimitiveLift hR v hv) =
      RhCompleteFormBound.boundedPart R C N (primitive R v) := by
  rw [boundedPart_apply, spatialPair_actual hR hv]
  unfold coshPair sinhPair
  rw [profilePair_actual hR hv _ (cosh_memLp R), profilePair_actual hR hv _ (sinh_memLp R)]
  simp_rw [shiftPair_actual hR hv]
  rfl

/-- The constructed complete bounded bilinear form has the ACTUAL physical
kernel diagonal, at every positive radius and every exact finite cutoff. -/
theorem completeForm_actual {R : ℝ} (hR : 0 < R) {v : ℝ → ℝ}
    (hv : MemLp v 2 (physicalMeasure R)) (N : ℕ) :
    completeForm R archConstant N
      (actualPrimitiveLift hR v hv) (actualPrimitiveLift hR v hv) =
      kernelQuadratic R (RhAllPrime.completeKernel N) v := by
  change archPair (actualPrimitiveLift hR v hv) (actualPrimitiveLift hR v hv) +
    boundedPart R archConstant N (actualPrimitiveLift hR v hv)
      (actualPrimitiveLift hR v hv) = _
  rw [archPair_diagonal, actualPrimitiveLift_physical, boundedPart_actual hR hv]
  exact (RhCompleteFormBound.actual_complete_decomposition hR hv N).symm

end RhNativeCompleteDictionary
#print axioms RhNativeCompleteDictionary.physicalVector_inner
#print axioms RhNativeCompleteDictionary.twoShift_spatial_dictionary
#print axioms RhNativeCompleteDictionary.physicalVector_shift
#print axioms RhNativeCompleteDictionary.boundedPart_actual
#print axioms RhNativeCompleteDictionary.completeForm_actual
