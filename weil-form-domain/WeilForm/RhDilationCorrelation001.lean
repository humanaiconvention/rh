import RhDilationFourier001

noncomputable section
open Set MeasureTheory Filter FourierTransform
open scoped Topology ComplexInnerProductSpace
namespace RhDilation

def correlation (f : ℝ → ℂ) (a : ℝ) : ℝ :=
  ∫ t : ℝ, (inner ℂ (f t) (f (t+a))).re

lemma inner_phase_real (z : ℂ) (theta : ℝ) :
    (inner ℂ z (Complex.exp ((theta:ℂ)*Complex.I)*z)).re =
      Real.cos theta * ‖z‖^2 := by
  rw [←smul_eq_mul,inner_smul_right,inner_self_eq_norm_sq_to_K]
  simp [pow_two,Complex.mul_re,Complex.mul_im,Complex.exp_re]

lemma correlation_integrable {f : ℝ → ℂ} (h2 : MemLp f 2 volume) (a : ℝ) :
    Integrable (fun t : ℝ => (inner ℂ (f t) (f (t+a))).re) volume := by
  have hs := translate_memLp h2 a
  have hi := (L2.integrable_inner (𝕜:=ℂ) (h2.toLp f)
    (hs.toLp (fun t => f (t+a)))).re
  apply hi.congr
  filter_upwards [h2.coeFn_toLp,hs.coeFn_toLp] with t ht hs'
  change (inner ℂ ((h2.toLp f) t) ((hs.toLp _) t)).re = _
  rw [ht,hs']

lemma correlation_spectral_integrable {f : ℝ → ℂ}
    (hf : Integrable f volume) (h2 : MemLp f 2 volume) (a : ℝ) :
    Integrable (fun ξ : ℝ => Real.cos (2*Real.pi*a*ξ)*
      RhTail.spectralDensity (h2.toLp f) ξ) volume := by
  have hs := translate_memLp h2 a
  have hi := (L2.integrable_inner (𝕜:=ℂ) (𝓕 (h2.toLp f))
    (𝓕 (hs.toLp (fun t => f (t+a))))).re
  apply hi.congr
  filter_upwards [fourier_translate_L2_ae hf h2 a] with ξ hξ
  change (inner ℂ ((𝓕 (h2.toLp f)) ξ)
    (((𝓕 (hs.toLp (fun t => f (t+a)))) : RhTail.WholeSpace) ξ)).re = _
  rw [hξ,inner_phase_real]
  rfl

/-- Exact shift/correlation Plancherel identity for the actual L1 and L2
function. Every use of an L2 representative is almost everywhere. -/
theorem correlation_plancherel {f : ℝ → ℂ}
    (hf : Integrable f volume) (h2 : MemLp f 2 volume) (a : ℝ) :
    correlation f a = ∫ ξ : ℝ, Real.cos (2*Real.pi*a*ξ)*
      RhTail.spectralDensity (h2.toLp f) ξ := by
  have hs := translate_memLp h2 a
  calc
    correlation f a = ∫ t : ℝ, (inner ℂ ((h2.toLp f) t)
        ((hs.toLp (fun t => f (t+a))) t)).re := by
      apply integral_congr_ae
      filter_upwards [h2.coeFn_toLp,hs.coeFn_toLp] with t ht hs'
      change (inner ℂ (f t) (f (t+a))).re = _
      rw [ht,hs']
    _ = ∫ ξ : ℝ, (inner ℂ ((𝓕 (h2.toLp f)) ξ)
        ((𝓕 (hs.toLp (fun t => f (t+a)))) ξ)).re :=
      (RhTail.real_inner_plancherel _ _).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [fourier_translate_L2_ae hf h2 a] with ξ hξ
      rw [hξ,inner_phase_real]
      rfl

end RhDilation
#print axioms RhDilation.inner_phase_real
#print axioms RhDilation.correlation_integrable
#print axioms RhDilation.correlation_spectral_integrable
#print axioms RhDilation.correlation_plancherel
