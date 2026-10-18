import RhWeightedShiftBilinear001
import RhDilationCorrelation001
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! Exact spatial/Fourier dictionary for the actual symmetric two-delay pairing.
Compact support is used only to prove L1 of actual L2 representatives. All
translation and quotient representative substitutions remain almost everywhere. -/
set_option maxHeartbeats 0
noncomputable section
open Set MeasureTheory Filter FourierTransform
open scoped Topology ComplexInnerProductSpace
namespace RhPhysicalShiftFourier
open RhWeightedMeasureEmbedding RhWeightedEnergyIdentity RhWeightedShiftBilinear

def spatialPair (u v : WholeSpace) (ell : ℝ) : ℝ :=
  ∫ t, inner ℝ (u t) (v (t + ell)) + inner ℝ (u t) (v (t - ell))

def spectralPair (u v : WholeSpace) (ell : ℝ) : ℝ :=
  ∫ xi, 2 * Real.cos ((2 * Real.pi * xi) * ell) *
    inner ℝ ((𝓕 u : WholeSpace) xi) ((𝓕 v : WholeSpace) xi)

lemma supported_integrable {R : ℝ} {F : WeightedSpace}
    (hF : F ∈ supportedSubspace R) : Integrable (physicalEmbedding F) volume := by
  have hI : IntegrableOn (physicalEmbedding F) (Icc (-R) R) volume :=
    integrableOn_Lp_of_measure_ne_top (physicalEmbedding F) (by norm_num)
      isCompact_Icc.measure_ne_top
  have hi : Integrable ((Icc (-R) R).indicator (physicalEmbedding F)) volume :=
    (integrable_indicator_iff measurableSet_Icc).mpr hI
  apply hi.congr
  filter_upwards [(mem_supportedSubspace_iff R F).mp hF] with t ht
  by_cases h : t ∈ Icc (-R) R
  · simp [h]
  · simp [h, ht h]

lemma inner_phase_pair (z w : ℂ) (theta : ℝ) :
    inner ℝ z (Complex.exp ((theta : ℂ) * Complex.I) * w) +
      inner ℝ z (Complex.exp (((-theta : ℝ) : ℂ) * Complex.I) * w) =
      2 * Real.cos theta * inner ℝ z w := by
  have he : Complex.exp ((theta : ℂ) * Complex.I) +
      Complex.exp (((-theta : ℝ) : ℂ) * Complex.I) = ((2 * Real.cos theta : ℝ) : ℂ) := by
    apply Complex.ext <;>
      simp [Complex.exp_re, Complex.exp_im, Complex.mul_re, Complex.mul_im, ← Complex.ofReal_cos]
    <;> ring
  calc
    _ = inner ℝ z ((Complex.exp ((theta : ℂ) * Complex.I) +
        Complex.exp (((-theta : ℝ) : ℂ) * Complex.I)) * w) := by
      rw [add_mul, inner_add_right]
    _ = _ := by
      rw [he]
      change inner ℝ z ((2 * Real.cos theta) • w) = _
      exact real_inner_smul_right _ _ _
lemma shifted_integrable (u v : WholeSpace) (ell : ℝ) :
    Integrable (fun t => inner ℝ (u t) (v (t + ell))) volume := by
  have hs := RhDilation.translate_memLp (Lp.memLp v) ell
  have hh := L2.integrable_inner (𝕜 := ℝ) u (hs.toLp (fun t => v (t + ell)))
  apply hh.congr
  filter_upwards [hs.coeFn_toLp] with t ht
  rw [ht]

lemma translated_phase_integrable (u v : WholeSpace)
    (hv : Integrable v volume) (ell : ℝ) :
    Integrable (fun xi => inner ℝ ((𝓕 u : WholeSpace) xi)
      (Complex.exp (((2 * Real.pi * ell * xi : ℝ) : ℂ) * Complex.I) *
        ((𝓕 v : WholeSpace) xi))) volume := by
  let hs := RhDilation.translate_memLp (Lp.memLp v) ell
  have hh := L2.integrable_inner (𝕜 := ℝ) (𝓕 u : WholeSpace)
    (𝓕 (hs.toLp (fun t => v (t + ell))) : WholeSpace)
  apply hh.congr
  filter_upwards [RhDilation.fourier_translate_L2_ae hv (Lp.memLp v) ell] with xi hxi
  rw [hxi, Lp.toLp_coeFn]

lemma translated_plancherel (u v : WholeSpace)
    (hv : Integrable v volume) (ell : ℝ) :
    (∫ t, inner ℝ (u t) (v (t + ell))) =
    ∫ xi, inner ℝ ((𝓕 u : WholeSpace) xi)
      (Complex.exp (((2 * Real.pi * ell * xi : ℝ) : ℂ) * Complex.I) *
        ((𝓕 v : WholeSpace) xi)) := by
  let hs := RhDilation.translate_memLp (Lp.memLp v) ell
  calc
    _ = ∫ t, inner ℝ (u t) ((hs.toLp (fun t => v (t + ell))) t) := by
      apply integral_congr_ae
      filter_upwards [hs.coeFn_toLp] with t ht
      rw [ht]
    _ = ∫ xi, inner ℝ ((𝓕 u : WholeSpace) xi)
        ((𝓕 (hs.toLp (fun t => v (t + ell))) : WholeSpace) xi) := by
      simp only [real_inner_eq_re_inner ℂ]
      change (∫ t, (inner ℂ (u t) ((hs.toLp (fun t => v (t + ell))) t)).re) =
        ∫ xi, (inner ℂ ((𝓕 u : WholeSpace) xi)
          ((𝓕 (hs.toLp (fun t => v (t + ell))) : WholeSpace) xi)).re
      exact (RhTail.real_inner_plancherel u (hs.toLp (fun t => v (t + ell)))).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [RhDilation.fourier_translate_L2_ae hv (Lp.memLp v) ell] with xi hxi
      rw [hxi, Lp.toLp_coeFn]

lemma phase_pair_identity (u v : WholeSpace) (ell xi : ℝ) :
    inner ℝ ((𝓕 u : WholeSpace) xi)
      (Complex.exp (((2 * Real.pi * ell * xi : ℝ) : ℂ) * Complex.I) *
        ((𝓕 v : WholeSpace) xi)) +
    inner ℝ ((𝓕 u : WholeSpace) xi)
      (Complex.exp (((2 * Real.pi * (-ell) * xi : ℝ) : ℂ) * Complex.I) *
        ((𝓕 v : WholeSpace) xi)) =
    2 * Real.cos ((2 * Real.pi * xi) * ell) *
      inner ℝ ((𝓕 u : WholeSpace) xi) ((𝓕 v : WholeSpace) xi) := by
  have h1 : 2 * Real.pi * ell * xi = (2 * Real.pi * xi) * ell := by ring
  have h2 : 2 * Real.pi * (-ell) * xi = -((2 * Real.pi * xi) * ell) := by ring
  rw [h1, h2]
  exact inner_phase_pair _ _ _

theorem spatial_spectral_dictionary (u v : WholeSpace) (hv : Integrable v volume)
    (ell : ℝ) :
    Integrable (fun xi => 2 * Real.cos ((2 * Real.pi * xi) * ell) *
      inner ℝ ((𝓕 u : WholeSpace) xi) ((𝓕 v : WholeSpace) xi)) volume ∧
    spatialPair u v ell = spectralPair u v ell := by
  have hp := translated_phase_integrable u v hv ell
  have hn := translated_phase_integrable u v hv (-ell)
  have hi : Integrable (fun xi => 2 * Real.cos ((2 * Real.pi * xi) * ell) *
      inner ℝ ((𝓕 u : WholeSpace) xi) ((𝓕 v : WholeSpace) xi)) volume :=
    (hp.add hn).congr (Eventually.of_forall (phase_pair_identity u v ell))
  refine ⟨hi, ?_⟩
  unfold spatialPair spectralPair
  have hminus : (fun t => inner ℝ (u t) (v (t - ell))) =
      (fun t => inner ℝ (u t) (v (t + (-ell)))) := by
    funext t
    rw [sub_eq_add_neg]
  simp_rw [sub_eq_add_neg]
  rw [integral_add (shifted_integrable u v ell) (shifted_integrable u v (-ell)),
    translated_plancherel u v hv ell, translated_plancherel u v hv (-ell),
    ← integral_add hp hn]
  apply integral_congr_ae
  exact Eventually.of_forall (phase_pair_identity u v ell)

/-- The actual supported spatial two-delay form is uniformly continuous in
the complete native weighted norm, including all quotient/AE identifications. -/
theorem uniform_supported_spatial_shift {eta : ℝ} (heta : 0 < eta) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ (R ell ell' : ℝ),
      |ell' - ell| < delta →
      ∀ (F G : WeightedSpace), F ∈ supportedSubspace R → G ∈ supportedSubspace R →
      |spatialPair (physicalEmbedding F) (physicalEmbedding G) ell' -
        spatialPair (physicalEmbedding F) (physicalEmbedding G) ell| ≤
        eta * ‖F‖ * ‖G‖ := by
  obtain ⟨delta, hdelta, hd⟩ := uniform_actual_shift_bilinear heta
  refine ⟨delta, hdelta, ?_⟩
  intro R ell ell' hshift F G _hF hG
  have hgi := supported_integrable hG
  obtain ⟨hi, he⟩ := spatial_spectral_dictionary (physicalEmbedding F) (physicalEmbedding G) hgi ell
  obtain ⟨hi', he'⟩ := spatial_spectral_dictionary (physicalEmbedding F) (physicalEmbedding G) hgi ell'
  have heq : spatialPair (physicalEmbedding F) (physicalEmbedding G) ell' -
      spatialPair (physicalEmbedding F) (physicalEmbedding G) ell =
      ∫ xi, shiftSymbol ell ell' xi *
        inner ℝ ((𝓕 (physicalEmbedding F) : WholeSpace) xi)
          ((𝓕 (physicalEmbedding G) : WholeSpace) xi) := by
    rw [he, he']
    unfold spectralPair shiftSymbol
    rw [← integral_sub hi' hi]
    congr 1
    funext xi
    ring
  rw [heq]
  exact (hd ell ell' hshift F G).2

end RhPhysicalShiftFourier
#print axioms RhPhysicalShiftFourier.supported_integrable
#print axioms RhPhysicalShiftFourier.spatial_spectral_dictionary
#print axioms RhPhysicalShiftFourier.uniform_supported_spatial_shift
