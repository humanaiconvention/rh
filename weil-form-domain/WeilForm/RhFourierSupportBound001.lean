import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import RhSupportedMollifier001

/-! Exact Fourier phase estimates for compact-support graph-domain compactness.
These are supporting analytic inequalities, not signed arithmetic estimates. -/
noncomputable section
open Set MeasureTheory Filter FourierTransform
open scoped Topology
namespace RhFourierSupportBound

def phase (x : ℝ) : ℂ := Complex.exp (Complex.I * (x : ℂ))

lemma phase_norm (x : ℝ) : ‖phase x‖ = 1 := by
  simp [phase, Complex.norm_exp, Complex.mul_re]

/-- Exact unitary phase Lipschitz bound with no real-part approximation. -/
lemma phase_lipschitz (x y : ℝ) : ‖phase x - phase y‖ ≤ |x - y| := by
  have he : phase x = phase y * phase (x - y) := by
    unfold phase
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  calc
    ‖phase x - phase y‖ = ‖phase y * (phase (x - y) - 1)‖ := by
      rw [he]
      congr 1
      ring
    _ = ‖phase (x - y) - 1‖ := by rw [norm_mul, phase_norm, one_mul]
    _ ≤ |x - y| := by
      simpa only [phase, Real.norm_eq_abs] using
        Real.norm_exp_I_mul_ofReal_sub_one_le (x := x - y)

lemma phase_mul_integrable {f : ℝ → ℂ} (hf : Integrable f volume) (xi : ℝ) :
    Integrable (fun t => phase (-2 * Real.pi * t * xi) * f t) volume := by
  apply hf.norm.mono'
  · exact (by unfold phase; fun_prop : Continuous (fun t : ℝ => phase (-2 * Real.pi * t * xi))).aestronglyMeasurable.mul
      hf.aestronglyMeasurable
  · exact Eventually.of_forall (fun t => by rw [norm_mul, phase_norm, one_mul])

/-- Lipschitz dependence of the ACTUAL compact-support Fourier transform.
No derivative or trace of the spatial function is required. -/
theorem fourier_lipschitz_of_support {R : ℝ} (hR : 0 ≤ R)
    {f : ℝ → ℂ} (hf : Integrable f volume)
    (hs : Function.support f ⊆ Icc (-R) R) (xi eta : ℝ) :
    ‖(𝓕 f) xi - (𝓕 f) eta‖ ≤
      (2 * Real.pi * R * |xi - eta|) * (∫ t, ‖f t‖) := by
  have hxi := phase_mul_integrable hf xi
  have heta := phase_mul_integrable hf eta
  have hmajor := hf.norm.const_mul (2 * Real.pi * R * |xi - eta|)
  have hconst : 0 ≤ 2 * Real.pi * R * |xi - eta| := by positivity
  have hpoint (t : ℝ) : ‖(phase (-2 * Real.pi * t * xi) -
      phase (-2 * Real.pi * t * eta)) * f t‖ ≤
        (2 * Real.pi * R * |xi - eta|) * ‖f t‖ := by
    by_cases ht : f t = 0
    · simp [ht]
    · have htR : |t| ≤ R := abs_le.mpr (hs ht)
      have hp := phase_lipschitz (-2 * Real.pi * t * xi) (-2 * Real.pi * t * eta)
      have heq : -2 * Real.pi * t * xi - -2 * Real.pi * t * eta =
          (-2 * Real.pi) * t * (xi - eta) := by ring
      rw [heq, abs_mul, abs_mul] at hp
      have hpi : |(-2 : ℝ) * Real.pi| = 2 * Real.pi := by
        rw [abs_of_nonpos (by nlinarith [Real.pi_pos])]
        ring
      rw [hpi] at hp
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_right hp (norm_nonneg _)).trans
        (by gcongr)
  have hfun : (fun t => phase (-2 * Real.pi * t * xi) * f t -
      phase (-2 * Real.pi * t * eta) * f t) =
      (fun t => (phase (-2 * Real.pi * t * xi) - phase (-2 * Real.pi * t * eta)) * f t) := by
    funext t
    ring
  have hdiff : Integrable (fun t => (phase (-2 * Real.pi * t * xi) -
      phase (-2 * Real.pi * t * eta)) * f t) volume := by
    rw [← hfun]
    exact hxi.sub heta
  have hFourier (z : ℝ) : (𝓕 f) z = ∫ t, phase (-2 * Real.pi * t * z) * f t := by
    rw [Real.fourier_real_eq_integral_exp_smul]
    apply integral_congr_ae
    exact Eventually.of_forall (fun t => by
      simp only [smul_eq_mul, phase, mul_comm Complex.I])
  rw [hFourier xi, hFourier eta, ← integral_sub hxi heta, hfun]
  calc
    _ ≤ ∫ t, ‖(phase (-2 * Real.pi * t * xi) - phase (-2 * Real.pi * t * eta)) * f t‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ t, (2 * Real.pi * R * |xi - eta|) * ‖f t‖ :=
      integral_mono hdiff.norm hmajor hpoint
    _ = _ := integral_const_mul _ _

end RhFourierSupportBound
#print axioms RhFourierSupportBound.phase_lipschitz
#print axioms RhFourierSupportBound.fourier_lipschitz_of_support
