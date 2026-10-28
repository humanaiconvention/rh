import RhWeilThetaGeometry001
import RhWeilThetaMeasurable001

/-! Unconditional coarse growth of the ACTUAL pole-removed completed zeta.
The logarithmic theta integrand is proved integrable with a Gaussian
majorant. No density theorem, explicit formula, or zero hypothesis is used. -/
set_option maxHeartbeats 0
noncomputable section
open Set Filter MeasureTheory
open scoped Topology FourierTransform
namespace RhWeilCompletedGrowth
open RhWeilThetaGeometry

def gaussianMass (p : ℝ) : ℝ := ∫u : ℝ, Real.exp (-(p/8)*u^2)

lemma gaussianMass_nonneg (p : ℝ) : 0≤gaussianMass p :=
  integral_nonneg (fun _=>(Real.exp_pos _).le)

lemma weighted_integrable {C p : ℝ} (hC : 0≤C) (hp : 0<p)
    (hh : ∀t:ℝ,1≤t→‖modif t‖≤C*Real.exp (-p*t)) (s : ℂ) :
    Integrable (fun u : ℝ=>Real.exp (-s.re*u) • modif (Real.exp (-u))) := by
  have hgauss := integrable_exp_neg_mul_sq (by positivity : 0<p/8)
  apply (hgauss.const_mul (C*Real.exp (2*(|s.re|+1/2)^2/p))).mono'
    (RhWeilTheta.weighted_modif_aestronglyMeasurable s)
  exact Eventually.of_forall (twisted_gaussian_bound hC hp hh s)

lemma mellin_norm_bound {C p : ℝ} (hC : 0≤C) (hp : 0<p)
    (hh : ∀t:ℝ,1≤t→‖modif t‖≤C*Real.exp (-p*t)) (s : ℂ) :
    ‖mellin modif s‖≤(C*gaussianMass p)*Real.exp (2*(|s.re|+1/2)^2/p) := by
  let F : ℝ → ℂ := fun u=>Real.exp (-s.re*u) • modif (Real.exp (-u))
  have hF : Integrable F := weighted_integrable hC hp hh s
  have hgauss := integrable_exp_neg_mul_sq (by positivity : 0<p/8)
  rw [mellin_eq_fourier]
  apply (Real.norm_fourier_le_integral_norm F _).trans
  calc
    _ ≤ ∫u : ℝ,(C*Real.exp (2*(|s.re|+1/2)^2/p))*Real.exp (-(p/8)*u^2) := by
      apply integral_mono hF.norm
        (hgauss.const_mul (C*Real.exp (2*(|s.re|+1/2)^2/p)))
      exact fun u=>twisted_gaussian_bound hC hp hh s u
    _ = _ := by rw [integral_const_mul];unfold gaussianMass;ring

/-- A deliberately weak quadratic exponential growth bound. Its finite
positive constants are obtained from proved theta decay and Gaussian integrals. -/
theorem completed_growth : ∃B:ℝ,0<B ∧ ∃D:ℝ,0<D ∧
    ∀s:ℂ,‖completedRiemannZeta₀ s‖≤B*Real.exp (D*(1+‖s‖)^2) := by
  obtain ⟨C,hC,p,hp,hh⟩ := RhWeilTheta.fePair_modif_head_bound
  have hhead : ∀t:ℝ,1≤t→‖modif t‖≤C*Real.exp (-p*t) := hh
  let B := C*gaussianMass p+1
  let D := 2/p
  have hCI : 0≤C*gaussianMass p := mul_nonneg hC.le (gaussianMass_nonneg p)
  have hB : 0<B := by dsimp [B];linarith
  have hD : 0<D := div_pos (by norm_num) hp
  refine ⟨B,hB,D,hD,fun s=>?_⟩
  have hm := mellin_norm_bound hC.le hp hhead (s/2)
  have hre : |(s/2).re|+1/2≤1+‖s‖ := by
    have hsre : (s/2).re=s.re/2 := by simp
    rw [hsre,abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)]
    have hr := Complex.abs_re_le_norm s
    nlinarith [norm_nonneg s]
  have hsqs : (|(s/2).re|+1/2)^2≤(1+‖s‖)^2 :=
    pow_le_pow_left₀ (by positivity) hre 2
  have he : Real.exp (2*(|(s/2).re|+1/2)^2/p)≤Real.exp (D*(1+‖s‖)^2) := by
    apply Real.exp_le_exp.mpr
    have h := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsqs
      (by norm_num : (0:ℝ)≤2)) hp.le
    convert h using 1 <;> dsimp [D] <;> ring
  change ‖mellin modif (s/2)/(2:ℂ)‖≤B*Real.exp (D*(1+‖s‖)^2)
  rw [norm_div,Complex.norm_ofNat]
  calc
    _ ≤ ((C*gaussianMass p)*Real.exp (2*(|(s/2).re|+1/2)^2/p))/2 :=
      div_le_div_of_nonneg_right hm (by norm_num)
    _ ≤ ((C*gaussianMass p)*Real.exp (D*(1+‖s‖)^2))/2 :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left he hCI) (by norm_num)
    _ ≤ _ := by
      dsimp [B]
      have he0 := Real.exp_pos (D*(1+‖s‖)^2)
      nlinarith

end RhWeilCompletedGrowth
#print axioms RhWeilCompletedGrowth.weighted_integrable
#print axioms RhWeilCompletedGrowth.mellin_norm_bound
#print axioms RhWeilCompletedGrowth.completed_growth
