import RhTranslatedJetCapacity001

/-! Exact physical representative of the actual translated capacity vectors.
Jet evaluation calculus is deliberately separate; the Fourier norm control
is tied here to the literal rescaled spatial profile, only almost everywhere.
-/
set_option maxHeartbeats 100000
noncomputable section
open Set MeasureTheory Filter FourierTransform
open scoped Topology
namespace RhTranslatedJetDictionary
open RhWeightedMeasureEmbedding RhWeightedDilationInverse RhTranslatedJetCapacity

lemma scalar_dilate_identity (j n : ℕ) (phi : ℝ → ℂ) (t x : ℝ) :
    (jetScalar j n : ℂ) * RhDilation.complexDilate (scale n)⁻¹ phi (t-x) =
      ((scale n ^ j)⁻¹ : ℂ) * phi ((t-x) * scale n) := by
  have hs : Real.sqrt (scale n) ≠ 0 := (Real.sqrt_pos.mpr (scale_pos n)).ne'
  have hcoef : jetScalar j n * Real.sqrt (scale n) = (scale n ^ j)⁻¹ := by
    unfold jetScalar
    rw [mul_assoc, inv_mul_cancel₀ hs, mul_one]
  simp only [RhDilation.complexDilate, Real.sqrt_inv, inv_inv, div_inv_eq_mul]
  calc
    _ = ((jetScalar j n * Real.sqrt (scale n) : ℝ) : ℂ) *
        phi ((t-x) * scale n) := by rw [Complex.ofReal_mul]; ring
    _ = _ := by rw [hcoef]; push_cast; rfl

/-- Actual complete-norm vectors have exactly the spatial profile needed
for point-jet tests. Point values of the arbitrary L2 representative are not
used: this statement is AE and its right side is the explicit smooth profile
when phi is smooth. -/
theorem jetVector_physical_ae {R : ℝ} (j : ℕ) (F : WeightedSpace)
    (hF : F ∈ supportedSubspace R) (x : ℝ) (n : ℕ) (phi : ℝ → ℂ)
    (hphi : physicalEmbedding F =ᵐ[volume] phi) :
    physicalEmbedding (jetVector j F hF x n) =ᵐ[volume]
      fun t => ((scale n ^ j)⁻¹ : ℂ) * phi ((t-x) * scale n) := by
  have hin := inwardLift_physical_ae (scale_ge_one n) F hF
  have hph := complexDilate_congr_ae (inv_pos.mpr (scale_pos n)) hphi
  have hh := hin.trans hph
  have hshift := (measurePreserving_add_right volume (-x)).quasiMeasurePreserving.ae hh
  have ht : physicalEmbedding (translatedInward F hF x n) =ᵐ[volume]
      fun t => RhDilation.complexDilate (scale n)⁻¹ phi (t-x) := by
    have htr := RhWeightedTranslation.translated_physical_ae
      (inwardLift (scale_ge_one n) F hF)
      (RhPhysicalShiftFourier.supported_integrable
        (inwardLift_supported (scale_ge_one n) F hF)) (-x)
    filter_upwards [htr, hshift] with t ht hs
    simpa only [translatedInward, sub_eq_add_neg] using ht.trans hs
  rw [jetVector, map_smul]
  filter_upwards [Lp.coeFn_smul (jetScalar j n)
    (physicalEmbedding (translatedInward F hF x n)), ht] with t hsm ht'
  rw [hsm]
  simp only [Pi.smul_apply, smul_eq_mul, ht']
  exact scalar_dilate_identity j n phi t x

end RhTranslatedJetDictionary
#print axioms RhTranslatedJetDictionary.scalar_dilate_identity
#print axioms RhTranslatedJetDictionary.jetVector_physical_ae

