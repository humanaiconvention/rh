import RhScaledMollifier001
import RhPhysicalShiftFourier001

/-! Literal spatial convolution for the already certified complete weighted
Fourier mollification. Compact representatives and all quotient equalities are
handled explicitly; no formal Fourier product is substituted without proof. -/
noncomputable section
open Set MeasureTheory Filter FourierTransform
open scoped Topology ContDiff Convolution
namespace RhSpatialMollifier
open RhWeightedMeasureEmbedding RhWeightedEnergyIdentity RhWeightedCoreAttempt
open RhWeightedMollifier RhScaledMollifier

def mollification (phi : ContDiffBump (0 : ℝ)) (n : ℕ) (f : ℝ → ℂ) : ℝ → ℂ :=
  scaledBump phi n ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] f

lemma mollification_contDiff (phi : ContDiffBump (0 : ℝ)) (n : ℕ)
    {f : ℝ → ℂ} (hf : Integrable f volume) :
    ContDiff ℝ ∞ (mollification phi n f) := by
  change ContDiff ℝ ∞ (scaledBump phi n ⋆[ContinuousLinearMap.mul ℝ ℂ, volume] f)
  exact (scaledBump_hasCompactSupport phi n).contDiff_convolution_left
    (ContinuousLinearMap.mul ℝ ℂ) (scaledBump_contDiff phi n) hf.locallyIntegrable

lemma mollification_hasCompactSupport (phi : ContDiffBump (0 : ℝ)) (n : ℕ)
    {f : ℝ → ℂ} (hf : HasCompactSupport f) :
    HasCompactSupport (mollification phi n f) :=
  (scaledBump_hasCompactSupport phi n).convolution (ContinuousLinearMap.mul ℂ ℂ) hf

lemma mollification_memLp (phi : ContDiffBump (0 : ℝ)) (n : ℕ)
    {f : ℝ → ℂ} (hf : Integrable f volume) (hcf : HasCompactSupport f) :
    MemLp (mollification phi n f) 2 volume :=
  (mollification_contDiff phi n hf).continuous.memLp_of_hasCompactSupport
    (mollification_hasCompactSupport phi n hcf)

lemma mollification_integrable (phi : ContDiffBump (0 : ℝ)) (n : ℕ)
    {f : ℝ → ℂ} (hf : Integrable f volume) (hcf : HasCompactSupport f) :
    Integrable (mollification phi n f) volume :=
  (mollification_contDiff phi n hf).continuous.integrable_of_hasCompactSupport
    (mollification_hasCompactSupport phi n hcf)

/-- Exact support radius for the physical convolution, not an asymptotic cell. -/
theorem mollification_tsupport (phi : ContDiffBump (0 : ℝ)) (n : ℕ)
    {R : ℝ} {f : ℝ → ℂ} (hs : Function.support f ⊆ Icc (-R) R) :
    tsupport (mollification phi n f) ⊆
      Icc (-(R + phi.rOut / scale n)) (R + phi.rOut / scale n) := by
  apply closure_minimal _ isClosed_Icc
  intro t ht
  have hsup := (support_convolution_subset (ContinuousLinearMap.mul ℂ ℂ)) ht
  obtain ⟨y, hy, z, hz, hsum⟩ := hsup
  have hyb := scaledBump_support_bound phi n hy
  have hzb := abs_le.mpr (hs hz)
  have hat : |t| ≤ R + phi.rOut / scale n := by
    rw [← hsum]
    exact (abs_add_le y z).trans (by linarith)
  exact abs_le.mp hat

/-- Actual convolution/Fourier identity, with exact normalized mollifier. -/
lemma mollification_fourier (phi : ContDiffBump (0 : ℝ)) (n : ℕ)
    {f : ℝ → ℂ} (hf : Integrable f volume) (xi : ℝ) :
    (𝓕 (mollification phi n f)) xi = bumpMultiplier phi n xi * (𝓕 f) xi := by
  rw [mollification, Real.fourier_mul_convolution_eq (scaledBump_integrable phi n) hf,
    scaledBump_fourier]

/-- The complete weighted multiplier really is the literal compact smooth
spatial convolution. The source identification is an L2 equality, not a bound. -/
theorem mollification_physical (phi : ContDiffBump (0 : ℝ)) (n : ℕ)
    (F : WeightedSpace) {f : ℝ → ℂ} (hf : Integrable f volume)
    (hcf : HasCompactSupport f) (hf2 : MemLp f 2 volume)
    (hF : physicalEmbedding F = hf2.toLp f) :
    physicalEmbedding (mollified phi n F) =
      (mollification_memLp phi n hf hcf).toLp (mollification phi n f) := by
  apply (Lp.fourierTransformₗᵢ ℝ ℂ).injective
  change (𝓕 (physicalEmbedding (mollified phi n F)) : WholeSpace) = _
  rw [physicalEmbedding_fourier]
  apply Lp.ext
  have hm : (mollified phi n F : ℝ → ℂ) =ᵐ[volume]
      fun xi => bumpMultiplier phi n xi * F xi :=
    (Measure.absolutelyContinuous_of_le volume_le_weightedMeasure).ae_eq
      (mollified_ae phi n F)
  have hraw : (𝓕 f) =ᵐ[volume] fun xi => F xi := by
    have h := RhTail.integral_fourier_ae_L2 hf hf2
    rw [← hF, physicalEmbedding_fourier] at h
    filter_upwards [h, inclusion_ae F] with xi hx hxi
    rw [hx, hxi]
  have hc := RhTail.integral_fourier_ae_L2
    (mollification_integrable phi n hf hcf) (mollification_memLp phi n hf hcf)
  filter_upwards [inclusion_ae (mollified phi n F), hm, hraw, hc] with xi hi hm' hf' hc'
  rw [hi, hm']
  change bumpMultiplier phi n xi * F xi =
    (𝓕 ((mollification_memLp phi n hf hcf).toLp (mollification phi n f)) : WholeSpace) xi
  rw [← hc', mollification_fourier phi n hf xi, hf']

end RhSpatialMollifier
#print axioms RhSpatialMollifier.mollification_tsupport
#print axioms RhSpatialMollifier.mollification_fourier
#print axioms RhSpatialMollifier.mollification_physical
