import RhWeightedMollifier001
import RhDilationFourier001
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Convolution

/-! Genuine compact smooth mass-one mollifiers underlying the already proved
weighted Fourier multiplier convergence. The Fourier scaling retains its
actual Jacobian and full complex phase. -/
noncomputable section
open Set MeasureTheory Filter FourierTransform
open scoped Topology ContDiff
namespace RhScaledMollifier
open RhWeightedCoreAttempt

def scale (n : ℕ) : ℝ := (n : ℝ) + 1
lemma scale_pos (n : ℕ) : 0 < scale n := by unfold scale; positivity

def scaledBump (phi : ContDiffBump (0 : ℝ)) (n : ℕ) (t : ℝ) : ℂ :=
  (scale n : ℂ) * bumpComplex phi (scale n * t)

lemma scaledBump_integrable (phi : ContDiffBump (0 : ℝ)) (n : ℕ) :
    Integrable (scaledBump phi n) volume :=
  ((bumpComplex_integrable phi).comp_mul_left' (scale_pos n).ne').const_mul _

lemma scaledBump_contDiff (phi : ContDiffBump (0 : ℝ)) (n : ℕ) :
    ContDiff ℝ ∞ (scaledBump phi n) := by
  have h : ContDiff ℝ ∞ (fun t : ℝ => phi.normed volume (scale n * t)) :=
    phi.contDiff_normed.comp (contDiff_const.mul contDiff_id)
  exact contDiff_const.mul (Complex.ofRealCLM.contDiff.comp h)

lemma scaledBump_support_bound (phi : ContDiffBump (0 : ℝ)) (n : ℕ)
    {t : ℝ} (ht : t ∈ Function.support (scaledBump phi n)) :
    |t| < phi.rOut / scale n := by
  have hs : bumpComplex phi (scale n * t) ≠ 0 := by
    intro hz
    apply ht
    simp [scaledBump, hz]
  have hn : phi.normed volume (scale n * t) ≠ 0 := by
    intro hz
    apply hs
    simp [bumpComplex, hz]
  have hb : scale n * t ∈ Metric.ball (0 : ℝ) phi.rOut := by
    rw [← phi.support_normed_eq (μ := volume)]
    exact hn
  have ha : |scale n * t| < phi.rOut := by
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using hb
  rw [abs_mul, abs_of_pos (scale_pos n)] at ha
  exact (lt_div_iff₀ (scale_pos n)).mpr (by nlinarith)

lemma scaledBump_hasCompactSupport (phi : ContDiffBump (0 : ℝ)) (n : ℕ) :
    HasCompactSupport (scaledBump phi n) := by
  apply HasCompactSupport.of_support_subset_isCompact
    (K := Icc (-(phi.rOut / scale n)) (phi.rOut / scale n)) isCompact_Icc
  intro t ht
  exact abs_le.mp (scaledBump_support_bound phi n ht).le

/-- Exact mass-one normalization at every finite index. -/
lemma scaledBump_integral (phi : ContDiffBump (0 : ℝ)) (n : ℕ) :
    (∫ t, scaledBump phi n t) = 1 := by
  unfold scaledBump
  rw [integral_const_mul, Measure.integral_comp_mul_left]
  rw [abs_of_pos (inv_pos.mpr (scale_pos n))]
  have hb : (∫ t, bumpComplex phi t) = 1 := by
    unfold bumpComplex
    rw [integral_complex_ofReal, phi.integral_normed]
    norm_num
  rw [hb]
  simp only [Complex.real_smul, mul_one]
  norm_cast
  exact mul_inv_cancel₀ (scale_pos n).ne'

/-- The actual spatial mollifier has exactly the multiplier already used in
weighted graph convergence, with no asymptotic or phase replacement. -/
theorem scaledBump_fourier (phi : ContDiffBump (0 : ℝ)) (n : ℕ) (xi : ℝ) :
    (𝓕 (scaledBump phi n)) xi = bumpMultiplier phi n xi := by
  unfold bumpMultiplier
  rw [Real.fourier_real_eq_integral_exp_smul, Real.fourier_real_eq_integral_exp_smul]
  simp only [smul_eq_mul]
  let g : ℝ → ℂ := fun t =>
    Complex.exp (((-2 * Real.pi * t * (xi / scale n) : ℝ) : ℂ) * Complex.I) * bumpComplex phi t
  have he : (fun t : ℝ => Complex.exp (((-2 * Real.pi * t * xi : ℝ) : ℂ) * Complex.I) *
      scaledBump phi n t) = fun t => (scale n : ℂ) * g (scale n * t) := by
    funext t
    dsimp only [scaledBump, g]
    have hphase : -2 * Real.pi * (scale n * t) * (xi / scale n) =
        -2 * Real.pi * t * xi := by field_simp [(scale_pos n).ne']
    rw [hphase]
    ring
  rw [he, integral_const_mul, Measure.integral_comp_mul_left,
    abs_of_pos (inv_pos.mpr (scale_pos n))]
  simp only [Complex.real_smul]
  rw [← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ (scale_pos n).ne', Complex.ofReal_one, one_mul]
  rfl

end RhScaledMollifier
#print axioms RhScaledMollifier.scaledBump_hasCompactSupport
#print axioms RhScaledMollifier.scaledBump_integral
#print axioms RhScaledMollifier.scaledBump_fourier
