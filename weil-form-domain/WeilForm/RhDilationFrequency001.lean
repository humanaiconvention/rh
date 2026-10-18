import RhDilationFourier001
import RhDilationScalar001
import RhPhysicalTailLimit001

noncomputable section
open Set MeasureTheory Filter FourierTransform
open scoped Topology BigOperators ENNReal
namespace RhDilation
open RhTail

def rawDensity (f : ℝ → ℂ) (ξ : ℝ) : ℝ := ‖(𝓕 f) ξ‖^2

def finiteMultiplier (b : ℝ) (K : ℕ) (ω : ℝ) : ℝ :=
  ∑ k ∈ Finset.range K, multiplier (ω^2) (b+2*k)

lemma rawDensity_ae {f : ℝ → ℂ} (hf : Integrable f volume) (h2 : MemLp f 2 volume) :
    rawDensity f =ᵐ[volume] spectralDensity (h2.toLp f) := by
  filter_upwards [integral_fourier_ae_L2 hf h2] with ξ hξ
  change ‖(𝓕 f) ξ‖^2 = ‖((𝓕 (h2.toLp f)):WholeSpace) ξ‖^2
  rw [hξ]

lemma rawDensity_integrable {f : ℝ → ℂ} (hf : Integrable f volume)
    (h2 : MemLp f 2 volume) : Integrable (rawDensity f) volume :=
  (spectralDensity_integrable (h2.toLp f)).congr (rawDensity_ae hf h2).symm

lemma rawDensity_norm_integral {f : ℝ → ℂ} (hf : Integrable f volume)
    (h2 : MemLp f 2 volume) :
    (∫ξ:ℝ,rawDensity f ξ)=∫t:ℝ,‖f t‖^2 := by
  rw [integral_congr_ae (rawDensity_ae hf h2)]
  exact norm_plancherel h2

lemma multiplier_upper {x b : ℝ} (hx : 0≤x) (hb : 0<b) :
    multiplier x b ≤ 2/b := by
  unfold multiplier
  have hd : 0<b*(b^2+x) := by positivity
  apply (div_le_iff₀ hd).2
  have he : (2/b)*(b*(b^2+x))=2*(b^2+x) := by field_simp <;> ring
  rw [he]
  nlinarith

lemma finiteMultiplier_nonneg {b:ℝ} (hb:0<b) (K:ℕ) (ω:ℝ) :
    0≤finiteMultiplier b K ω := by
  exact Finset.sum_nonneg (fun k _=>multiplier_nonneg (sq_nonneg ω) (by positivity))

lemma finiteMultiplier_upper {b:ℝ} (hb:0<b) (K:ℕ) (ω:ℝ) :
    finiteMultiplier b K ω≤∑k∈Finset.range K,2/(b+2*k) := by
  exact Finset.sum_le_sum (fun k _=>multiplier_upper (sq_nonneg ω) (by positivity))

lemma finiteMultiplier_continuous {b:ℝ} (hb:0<b) (K:ℕ) :
    Continuous (finiteMultiplier b K) := by
  unfold finiteMultiplier
  apply continuous_finset_sum
  intro k hk
  unfold multiplier
  apply Continuous.div
  · fun_prop
  · fun_prop
  · intro ω
    exact ne_of_gt (by positivity)

lemma finite_density_integrable {f:ℝ→ℂ} (hf:Integrable f volume)
    (h2:MemLp f 2 volume) {b:ℝ} (hb:0<b) (K:ℕ) (scale:ℝ) :
    Integrable (fun ξ:ℝ=>finiteMultiplier b K (2*Real.pi*ξ/scale)*rawDensity f ξ) volume := by
  apply (rawDensity_integrable hf h2).bdd_mul (c:=∑k∈Finset.range K,2/(b+2*k))
    ((finiteMultiplier_continuous hb K).comp (by fun_prop)).aestronglyMeasurable
  exact Eventually.of_forall (fun ξ=>by
    dsimp only [Function.comp_apply]
    rw [Real.norm_eq_abs,abs_of_nonneg (finiteMultiplier_nonneg hb K _)]
    exact finiteMultiplier_upper hb K _)

lemma rawDensity_dilate {r:ℝ} (hr:0<r) (f:ℝ→ℂ) (ξ:ℝ) :
    rawDensity (complexDilate r f) ξ=r*rawDensity f (r*ξ) := by
  unfold rawDensity
  rw [fourier_complexDilate hr,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (Real.sqrt_pos.2 hr),mul_pow,Real.sq_sqrt hr.le]

/-- The non-volume-preserving Fourier substitution includes its exact Jacobian. -/
theorem finite_energy_dilate {r:ℝ} (hr:0<r) (f:ℝ→ℂ) (b:ℝ) (K:ℕ) :
    (∫ξ:ℝ,finiteMultiplier b K (2*Real.pi*ξ)*rawDensity (complexDilate r f) ξ)=
      ∫ξ:ℝ,finiteMultiplier b K (2*Real.pi*ξ/r)*rawDensity f ξ := by
  let g:ℝ→ℝ:=fun ξ=>finiteMultiplier b K (2*Real.pi*ξ/r)*rawDensity f ξ
  have he : (fun ξ:ℝ=>finiteMultiplier b K (2*Real.pi*ξ)*rawDensity (complexDilate r f) ξ)=
      fun ξ=>r*g (r*ξ) := by
    funext ξ
    dsimp only [g]
    rw [rawDensity_dilate hr]
    have hω : 2*Real.pi*(r*ξ)/r=2*Real.pi*ξ := by field_simp
    rw [hω]
    ring
  rw [he,integral_const_mul,Measure.integral_comp_mul_left]
  simp only [smul_eq_mul]
  change r * (|r⁻¹| * (∫ξ:ℝ,g ξ)) = ∫ξ:ℝ,g ξ
  rw [abs_of_pos (inv_pos.mpr hr)]
  field_simp [ne_of_gt hr]

/-- Signed finite multiplier comparison; no arithmetic phases are discarded. -/
theorem finite_energy_scaling {r b:ℝ} (hr:1≤r) (hb:0<b)
    {f:ℝ→ℂ} (hf:Integrable f volume) (h2:MemLp f 2 volume) (K:ℕ) :
    (∫ξ:ℝ,finiteMultiplier b K (2*Real.pi*ξ)*rawDensity f ξ) ≤
      (∫ξ:ℝ,finiteMultiplier b K (2*Real.pi*ξ)*rawDensity (complexDilate r f) ξ)+
      ((1+2/b)*Real.log r)*(∫t:ℝ,‖f t‖^2) := by
  have hrp:0<r:=by linarith
  rw [finite_energy_dilate hrp]
  have hi0 := finite_density_integrable hf h2 hb K 1
  simp only [div_one] at hi0
  have hi1 := finite_density_integrable hf h2 hb K r
  have hi2 := (rawDensity_integrable hf h2).const_mul ((1+2/b)*Real.log r)
  calc
    _ ≤ ∫ξ:ℝ,finiteMultiplier b K (2*Real.pi*ξ/r)*rawDensity f ξ+
        ((1+2/b)*Real.log r)*rawDensity f ξ := by
      apply integral_mono hi0 (hi1.add hi2)
      intro ξ
      dsimp only [Pi.add_apply]
      have hm := (RhDilationScalar.finite_multiplier_scaling hb hr (2*Real.pi*ξ) K).2
      have hd:0≤rawDensity f ξ:=sq_nonneg _
      unfold finiteMultiplier at *
      nlinarith [mul_le_mul_of_nonneg_right hm hd]
    _ = _ := by
      rw [integral_add hi1 hi2,integral_const_mul,rawDensity_norm_integral hf h2]

lemma finite_energy_frequency {b:ℝ} (hb:0<b) {f:ℝ→ℂ}
    (hf:Integrable f volume) (h2:MemLp f 2 volume) (K:ℕ) :
    finiteFrequencyEnergy b (h2.toLp f) K=
      ENNReal.ofReal (∫ξ:ℝ,finiteMultiplier b K (2*Real.pi*ξ)*rawDensity f ξ) := by
  have hi:=finite_density_integrable hf h2 hb K 1
  simp only [div_one] at hi
  rw [ofReal_integral_eq_lintegral_ofReal hi]
  · unfold finiteFrequencyEnergy
    apply lintegral_congr_ae
    filter_upwards [rawDensity_ae hf h2] with ξ hξ
    rw [hξ]
    have hn:∀k∈Finset.range K,0≤multiplier (angularSquare ξ) (b+2*k)*spectralDensity (h2.toLp f) ξ :=
      fun k _=>mul_nonneg (multiplier_nonneg (sq_nonneg _) (by positivity)) (sq_nonneg _)
    simp only [finiteMultiplier,Finset.sum_mul,angularSquare]
    exact (ENNReal.ofReal_sum_of_nonneg hn).symm
  · exact Eventually.of_forall (fun ξ=>mul_nonneg (finiteMultiplier_nonneg hb K _) (sq_nonneg _))

end RhDilation
#print axioms RhDilation.rawDensity_ae
#print axioms RhDilation.finite_energy_dilate
#print axioms RhDilation.finite_energy_scaling
#print axioms RhDilation.finite_energy_frequency






