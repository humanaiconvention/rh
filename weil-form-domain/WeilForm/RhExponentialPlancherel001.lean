import RhExponentialConvolution001

noncomputable section
open MeasureTheory Filter FourierTransform
open scoped Topology BigOperators ENNReal ComplexInnerProductSpace
namespace RhTail

lemma inner_real_scalar (a : ℝ) (z : ℂ) :
    (inner ℂ z ((a : ℂ)*z)).re = a*‖z‖^2 := by
  change RCLike.re (inner ℂ z (a • z)) = _
  rw [← real_inner_eq_re_inner ℂ, real_inner_smul_right, real_inner_self_eq_norm_sq]

lemma real_inner_plancherel (F G : WholeSpace) :
    (∫ ξ : ℝ, (inner ℂ ((𝓕 F) ξ) ((𝓕 G) ξ)).re) =
      ∫ t : ℝ, (inner ℂ (F t) (G t)).re := by
  calc
    _ = (inner ℂ (𝓕 F) (𝓕 G)).re :=
      integral_re (L2.integrable_inner (𝕜 := ℂ) (𝓕 F) (𝓕 G))
    _ = (inner ℂ F G).re := congrArg Complex.re (plancherel_inner F G)
    _ = _ := (integral_re (L2.integrable_inner (𝕜 := ℂ) F G)).symm

lemma spectralDensity_integrable (F : WholeSpace) :
    Integrable (spectralDensity F) volume :=
  (memLp_two_iff_integrable_sq_norm (Lp.memLp (𝓕 F)).aestronglyMeasurable).mp
    (Lp.memLp (𝓕 F))

theorem norm_plancherel {f : ℝ → ℂ} (h2 : MemLp f 2 volume) :
    (∫ ξ : ℝ, spectralDensity (h2.toLp f) ξ) = ∫ t : ℝ, ‖f t‖^2 := by
  have hp := real_inner_plancherel (h2.toLp f) (h2.toLp f)
  calc
    _ = ∫ ξ : ℝ, (inner ℂ ((𝓕 (h2.toLp f)) ξ) ((𝓕 (h2.toLp f)) ξ)).re := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun ξ => (norm_sq_eq_re_inner (𝕜 := ℂ) _))
    _ = _ := hp
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [h2.coeFn_toLp] with t ht
      rw [ht]
      exact (norm_sq_eq_re_inner (𝕜 := ℂ) (f t)).symm

lemma exponential_spectral_pair_integrable {β : ℝ} (hβ : 0 < β)
    {f : ℝ → ℂ} (hf : Integrable f volume) (h2 : MemLp f 2 volume) :
    Integrable (fun ξ : ℝ => (2*β/(β^2+angularSquare ξ))*
      spectralDensity (h2.toLp f) ξ) volume := by
  apply ((L2.integrable_inner (𝕜 := ℂ) (𝓕 (h2.toLp f))
    (𝓕 ((exponentialConvolution_memLp hβ hf).toLp (exponentialConvolution β f)))).re).congr
  filter_upwards [exponentialConvolution_fourier_ae hβ hf h2] with ξ hξ
  rw [hξ]
  exact inner_real_scalar _ _

theorem exponential_pair_plancherel {β : ℝ} (hβ : 0 < β)
    {f : ℝ → ℂ} (hf : Integrable f volume) (h2 : MemLp f 2 volume) :
    (∫ ξ : ℝ, (2*β/(β^2+angularSquare ξ))*spectralDensity (h2.toLp f) ξ) =
      ∫ t : ℝ, (inner ℂ (f t) (exponentialConvolution β f t)).re := by
  calc
    _ = ∫ ξ : ℝ, (inner ℂ ((𝓕 (h2.toLp f)) ξ)
        ((𝓕 ((exponentialConvolution_memLp hβ hf).toLp
          (exponentialConvolution β f))) ξ)).re := by
      apply integral_congr_ae
      filter_upwards [exponentialConvolution_fourier_ae hβ hf h2] with ξ hξ
      rw [hξ, inner_real_scalar]
      rfl
    _ = _ := real_inner_plancherel _ _
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [h2.coeFn_toLp, (exponentialConvolution_memLp hβ hf).coeFn_toLp] with t ht hg
      rw [ht, hg]

lemma multiplier_difference {β : ℝ} (hβ : 0 < β) (ξ : ℝ) :
    2/β-2*β/(β^2+angularSquare ξ) = multiplier (angularSquare ξ) β := by
  have hd : β^2+angularSquare ξ ≠ 0 := ne_of_gt (by
    unfold angularSquare
    positivity)
  unfold multiplier
  field_simp
  <;> ring

lemma multiplier_energy_integrable {β : ℝ} (hβ : 0 < β)
    {f : ℝ → ℂ} (hf : Integrable f volume) (h2 : MemLp f 2 volume) :
    Integrable (fun ξ : ℝ => multiplier (angularSquare ξ) β*
      spectralDensity (h2.toLp f) ξ) volume := by
  apply ((spectralDensity_integrable (h2.toLp f)).const_mul (2/β)).sub
    (exponential_spectral_pair_integrable hβ hf h2) |>.congr
  exact Eventually.of_forall (fun ξ => by
    simp only [Pi.sub_apply]
    rw [← sub_mul, multiplier_difference hβ])

theorem exponential_difference_plancherel {β : ℝ} (hβ : 0 < β)
    {f : ℝ → ℂ} (hf : Integrable f volume) (h2 : MemLp f 2 volume) :
    (2/β)*(∫ t : ℝ, ‖f t‖^2) -
      (∫ t : ℝ, (inner ℂ (f t) (exponentialConvolution β f t)).re) =
    ∫ ξ : ℝ, multiplier (angularSquare ξ) β*spectralDensity (h2.toLp f) ξ := by
  rw [← norm_plancherel h2, ← exponential_pair_plancherel hβ hf h2, ← integral_const_mul,
    ← integral_sub ((spectralDensity_integrable _).const_mul _)
      (exponential_spectral_pair_integrable hβ hf h2)]
  apply integral_congr_ae
  exact Eventually.of_forall (fun ξ => by
    dsimp only
    rw [← sub_mul, multiplier_difference hβ])

end RhTail
#print axioms RhTail.exponential_difference_plancherel
#print axioms RhTail.exponential_pair_plancherel
