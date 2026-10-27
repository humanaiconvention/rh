import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# Classical Gauss digamma difference: isolated extraction candidate

This file collects the generic closure of the five audited source modules.
Namespaces are renamed; the native quarter-normalization corollary is omitted.
The explicit-integrand integrability corollary is added.  See SOURCE-MAP.json
and PROVENANCE.md for exact provenance and the scope of verification.
No mathematical novelty or submission readiness is asserted.
-/

/-! ## Extracted from RhWeilBetaDomination001.lean -/
/-! The cancelled Beta difference has a genuine parameter-independent
integrable dominator. The right endpoint is controlled through the actual
continuous divided difference, retaining the cancellation before estimation. -/
set_option maxHeartbeats 0
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace DigammaGauss.BetaDomination

def powerDiff (a : ℝ) (z : ℂ) (t : ℝ) : ℂ :=
  (t : ℂ)^((a : ℂ)-1)-(t : ℂ)^(z-1)

def betaDifferenceIntegrand (a : ℝ) (z : ℂ) (h t : ℝ) : ℂ :=
  powerDiff a z t * (1-(t : ℂ))^((h : ℂ)-1)

def limitKernel (a : ℝ) (z : ℂ) (t : ℝ) : ℂ :=
  powerDiff a z t / (1-(t : ℂ))

@[simp] lemma powerDiff_one (a : ℝ) (z : ℂ) : powerDiff a z 1=0 := by
  simp [powerDiff]

lemma powerDiff_differentiableAt (a : ℝ) (z : ℂ) {t : ℝ} (ht : 0<t) :
    DifferentiableAt ℝ (powerDiff a z) t := by
  have h1 := (Complex.hasStrictDerivAt_cpow_const
    (c:=(a : ℂ)-1) (Complex.ofReal_mem_slitPlane.mpr ht)).hasDerivAt.comp_ofReal
  have h2 := (Complex.hasStrictDerivAt_cpow_const
    (c:=z-1) (Complex.ofReal_mem_slitPlane.mpr ht)).hasDerivAt.comp_ofReal
  exact (h1.sub h2).differentiableAt

/-- A finite right-half cancellation constant is constructed from the
compact image of the continuous divided difference, not supplied as a hypothesis. -/
theorem exists_right_cancel_bound (a : ℝ) (z : ℂ) :
    ∃ C : ℝ, 0<C ∧ ∀ t ∈ Icc (1/2 : ℝ) 1,
      ‖powerDiff a z t‖ ≤ C*(1-t) := by
  have hslope : ContinuousOn (dslope (powerDiff a z) 1) (Icc (1/2 : ℝ) 1) := by
    intro t ht
    by_cases ht1 : t=1
    · subst t
      exact (continuousAt_dslope_same.mpr
        (powerDiff_differentiableAt a z (by norm_num))).continuousWithinAt
    · exact ((continuousAt_dslope_of_ne ht1).mpr
        (powerDiff_differentiableAt a z (by linarith [ht.1])).continuousAt).continuousWithinAt
  obtain ⟨B,hB⟩ := isCompact_Icc.bddAbove_image hslope.norm
  let C : ℝ := max B 0+1
  have hC : 0<C := by dsimp [C]; linarith [le_max_right B 0]
  refine ⟨C,hC,?_⟩
  intro t ht
  have hBC : B≤C := by dsimp [C]; linarith [le_max_left B 0]
  have hb : ‖dslope (powerDiff a z) 1 t‖≤C :=
    (hB (mem_image_of_mem _ ht)).trans hBC
  have heq := congrArg norm (sub_smul_dslope (powerDiff a z) 1 t)
  simp only [powerDiff_one,sub_zero,norm_smul,Real.norm_eq_abs] at heq
  rw [abs_of_nonpos (by linarith [ht.2] : t-1≤0)] at heq
  calc
    _ = (1-t)*‖dslope (powerDiff a z) 1 t‖ := by linarith [heq]
    _ ≤ (1-t)*C := mul_le_mul_of_nonneg_left hb (by linarith [ht.2])
    _ = _ := by ring

lemma powerDiff_norm_le (a : ℝ) (z : ℂ) {t : ℝ} (ht : 0<t) :
    ‖powerDiff a z t‖ ≤ t^(a-1)+t^(z.re-1) := by
  have h := norm_sub_le ((t : ℂ)^((a : ℂ)-1)) ((t : ℂ)^(z-1))
  simpa only [powerDiff,Complex.norm_cpow_eq_rpow_re_of_pos ht,
    Complex.sub_re,Complex.ofReal_re,Complex.one_re] using h

lemma betaFactor_norm_le {h t : ℝ} (hh : 0≤h) (ht : t∈Ioo (0 : ℝ) 1) :
    ‖(1-(t : ℂ))^((h : ℂ)-1)‖ ≤ (1-t)⁻¹ := by
  have hb : 0<1-t := by linarith [ht.2]
  have he : (1-(t : ℂ))=((1-t : ℝ) : ℂ) := by push_cast; rfl
  rw [he,Complex.norm_cpow_eq_rpow_re_of_pos hb]
  simp only [Complex.sub_re,Complex.ofReal_re,Complex.one_re]
  simpa only [Real.rpow_neg_one] using
    Real.rpow_le_rpow_of_exponent_ge hb (by linarith [ht.1] : 1-t≤1)
      (by linarith : (-1 : ℝ)≤h-1)

/-- This piecewise dominator retains both endpoint mechanisms. -/
def dominator (a : ℝ) (z : ℂ) (C t : ℝ) : ℝ :=
  if t≤1/2 then 2*(t^(a-1)+t^(z.re-1)) else C

lemma dominated {a : ℝ} {z : ℂ} {C : ℝ}
    (hC : ∀ t∈Icc (1/2 : ℝ) 1, ‖powerDiff a z t‖≤C*(1-t))
    {h t : ℝ} (hh : 0≤h) (ht : t∈Ioo (0 : ℝ) 1) :
    ‖betaDifferenceIntegrand a z h t‖≤dominator a z C t := by
  unfold betaDifferenceIntegrand dominator
  rw [norm_mul]
  have hb := betaFactor_norm_le hh ht
  by_cases ht2 : t≤1/2
  · rw [if_pos ht2]
    have hi : (1-t)⁻¹≤2 := by
      apply (inv_le_comm₀ (by linarith [ht.2] : 0<1-t) (by norm_num : (0 : ℝ)<2)).mpr
      nlinarith
    calc
      _ ≤ ‖powerDiff a z t‖*2 := mul_le_mul_of_nonneg_left (hb.trans hi) (norm_nonneg _)
      _ ≤ (t^(a-1)+t^(z.re-1))*2 := mul_le_mul_of_nonneg_right (powerDiff_norm_le a z ht.1) (by norm_num)
      _ = _ := by ring
  · rw [if_neg ht2]
    have hr := hC t ⟨by linarith,ht.2.le⟩
    calc
      _ ≤ (C*(1-t))*(1-t)⁻¹ := mul_le_mul hr hb (norm_nonneg _) (by linarith [norm_nonneg (powerDiff a z t)])
      _ = C := by rw [mul_assoc,mul_inv_cancel₀ (by linarith [ht.2] : 1-t≠0),mul_one]

lemma dominator_integrable {a : ℝ} {z : ℂ} (ha : 0<a) (hz : 0<z.re) (C : ℝ) :
    IntegrableOn (dominator a z C) (Ioo (0 : ℝ) 1) := by
  classical
  have haI := (intervalIntegral.integrableOn_Ioo_rpow_iff (by norm_num : (0 : ℝ)<1)).mpr
    (by linarith : (-1 : ℝ)<a-1)
  have hzI := (intervalIntegral.integrableOn_Ioo_rpow_iff (by norm_num : (0 : ℝ)<1)).mpr
    (by linarith : (-1 : ℝ)<z.re-1)
  have hleft := (haI.add hzI).const_mul 2
  have hright : IntegrableOn (fun _ : ℝ => C) (Ioo (0 : ℝ) 1) := integrableOn_const measure_Ioo_lt_top.ne
  exact Integrable.piecewise measurableSet_Iic.nullMeasurableSet hleft.integrableOn hright.integrableOn

end DigammaGauss.BetaDomination
end -- close the source module noncomputable section
#print axioms DigammaGauss.BetaDomination.exists_right_cancel_bound
#print axioms DigammaGauss.BetaDomination.dominated
#print axioms DigammaGauss.BetaDomination.dominator_integrable

/-! ## Extracted from RhWeilBetaLimit001.lean -/
/-! Dominated convergence for the actual cancelled Beta difference.
Endpoint values are handled through the restricted open-interval measure. -/
set_option maxHeartbeats 0
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace DigammaGauss.BetaLimit
open DigammaGauss.BetaDomination

lemma integrand_continuousOn (a : ℝ) (z : ℂ) (h : ℝ) :
    ContinuousOn (betaDifferenceIntegrand a z h) (Ioo (0 : ℝ) 1) := by
  have hp (w : ℂ) : ContinuousOn (fun t : ℝ => (t : ℂ)^w) (Ioo (0 : ℝ) 1) :=
    Complex.continuous_ofReal.continuousOn.cpow_const (fun t ht => Complex.ofReal_mem_slitPlane.mpr ht.1)
  have hb : ContinuousOn (fun t : ℝ => (1-(t : ℂ))^((h : ℂ)-1)) (Ioo (0 : ℝ) 1) :=
    (continuous_const.sub Complex.continuous_ofReal).continuousOn.cpow_const (fun t ht => by
      apply Complex.mem_slitPlane_iff.mpr
      left
      change 0 < 1-t
      linarith [ht.2])
  exact ((hp ((a : ℂ)-1)).sub (hp (z-1))).mul hb

lemma integrand_zero (a : ℝ) (z : ℂ) (t : ℝ) :
    betaDifferenceIntegrand a z 0 t=limitKernel a z t := by
  simp [betaDifferenceIntegrand,limitKernel,Complex.cpow_neg_one,div_eq_mul_inv]

lemma integrand_tendsto (a : ℝ) (z : ℂ) (t : ℝ) :
    Tendsto (fun h : ℝ => betaDifferenceIntegrand a z h t) (𝓝[>] 0) (𝓝 (limitKernel a z t)) := by
  have hh : Tendsto (fun h : ℝ => (h : ℂ)-1) (𝓝[>] 0) (𝓝 (-1 : ℂ)) := by
    have hc : ContinuousAt (fun h : ℝ => (h : ℂ)-1) 0 := by fun_prop
    simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
  have hp := hh.const_cpow (a:=1-(t : ℂ)) (Or.inr (by norm_num : (-1 : ℂ)≠0))
  simpa only [betaDifferenceIntegrand,limitKernel,Complex.cpow_neg_one,div_eq_mul_inv] using
    tendsto_const_nhds.mul hp

/-- The limiting integrand is genuinely integrable, retaining both endpoints. -/
theorem limitKernel_integrable {a : ℝ} {z : ℂ} (ha : 0<a) (hz : 0<z.re) :
    IntegrableOn (limitKernel a z) (Ioo (0 : ℝ) 1) := by
  obtain ⟨C,hC,hB⟩ := exists_right_cancel_bound a z
  have hMeas : AEStronglyMeasurable (limitKernel a z) (volume.restrict (Ioo (0 : ℝ) 1)) := by
    have h := (integrand_continuousOn a z 0).aestronglyMeasurable (μ:=volume) measurableSet_Ioo
    have he : betaDifferenceIntegrand a z 0 = limitKernel a z := funext (integrand_zero a z)
    rwa [he] at h
  apply (dominator_integrable ha hz C).mono' hMeas
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  simpa only [integrand_zero] using dominated hB (h:=0) (by norm_num) ht

/-- DCT is applied to the complete difference before either endpoint is
estimated. The dominator is fixed while the real h decreases to zero. -/
theorem cancelled_integral_limit {a : ℝ} {z : ℂ} (ha : 0<a) (hz : 0<z.re) :
    Tendsto (fun h : ℝ => ∫ t in Ioo (0 : ℝ) 1, betaDifferenceIntegrand a z h t)
      (𝓝[>] 0) (𝓝 (∫ t in Ioo (0 : ℝ) 1, limitKernel a z t)) := by
  obtain ⟨C,hC,hB⟩ := exists_right_cancel_bound a z
  apply tendsto_integral_filter_of_dominated_convergence (dominator a z C)
  · exact Eventually.of_forall (fun h => (integrand_continuousOn a z h).aestronglyMeasurable measurableSet_Ioo)
  · filter_upwards [self_mem_nhdsWithin] with h hh
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact dominated hB (le_of_lt hh) ht
  · exact dominator_integrable ha hz C
  · exact Eventually.of_forall (fun t => integrand_tendsto a z t)

lemma beta_difference_eq_integral {a : ℝ} {z : ℂ} (ha : 0<a) (hz : 0<z.re)
    {h : ℝ} (hh : 0<h) :
    Complex.betaIntegral (a : ℂ) (h : ℂ)-Complex.betaIntegral z (h : ℂ)=
      ∫ t in Ioo (0 : ℝ) 1, betaDifferenceIntegrand a z h t := by
  have haI := Complex.betaIntegral_convergent (u:=(a : ℂ)) (v:=(h : ℂ)) (by simpa using ha) (by simpa using hh)
  have hzI := Complex.betaIntegral_convergent (u:=z) (v:=(h : ℂ)) hz (by simpa using hh)
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (0 : ℝ)≤1)] at haI hzI
  unfold Complex.betaIntegral
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ)≤1),
    intervalIntegral.integral_of_le (by norm_num : (0 : ℝ)≤1),
    integral_Ioc_eq_integral_Ioo,integral_Ioc_eq_integral_Ioo,←integral_sub haI hzI]
  apply integral_congr_ae
  exact Eventually.of_forall (fun t => by
    dsimp only [betaDifferenceIntegrand,powerDiff]
    ring)

/-- Exact integral-side limit for the same Beta difference as the Gamma
ratio theorem. It has no additional domination or convergence premise. -/
theorem beta_difference_integral_limit {a : ℝ} {z : ℂ} (ha : 0<a) (hz : 0<z.re) :
    Tendsto (fun h : ℝ => Complex.betaIntegral (a : ℂ) (h : ℂ)-Complex.betaIntegral z (h : ℂ))
      (𝓝[>] 0) (𝓝 (∫ t in Ioo (0 : ℝ) 1, limitKernel a z t)) := by
  apply (cancelled_integral_limit ha hz).congr'
  filter_upwards [self_mem_nhdsWithin] with h hh
  exact (beta_difference_eq_integral ha hz hh).symm

end DigammaGauss.BetaLimit
end -- close the source module noncomputable section
#print axioms DigammaGauss.BetaLimit.limitKernel_integrable
#print axioms DigammaGauss.BetaLimit.cancelled_integral_limit
#print axioms DigammaGauss.BetaLimit.beta_difference_eq_integral
#print axioms DigammaGauss.BetaLimit.beta_difference_integral_limit

/-! ## Extracted from RhWeilGaussSubstitution001.lean -/
/-! Exact logarithmic change of variables from the cancelled Beta-domain
kernel to the Gauss half-line kernel. The positive Jacobian is retained. -/
set_option maxHeartbeats 0
noncomputable section
open Set MeasureTheory
open scoped Topology
namespace DigammaGauss.Substitution
open DigammaGauss.BetaDomination

lemma image_exp_neg : (fun x : ℝ => Real.exp (-x)) '' Ioi (0 : ℝ)=Ioo (0 : ℝ) 1 := by
  ext t
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact ⟨Real.exp_pos _,Real.exp_lt_one_iff.mpr (by have hp : 0<x := hx; linarith)⟩
  · intro ht
    refine ⟨-Real.log t,?_,?_⟩
    · exact neg_pos.mpr (Real.log_neg ht.1 ht.2)
    · dsimp only
      rw [neg_neg,Real.exp_log ht.1]

lemma exp_neg_deriv (x : ℝ) :
    HasDerivAt (fun y : ℝ => Real.exp (-y)) (-Real.exp (-x)) x := by
  simpa using (hasDerivAt_neg x).exp

lemma exp_neg_injective : Function.Injective (fun x : ℝ => Real.exp (-x)) := by
  intro x y h
  exact neg_injective (Real.exp_injective h)

/-- A genuine change of variables for arbitrary complex integrands. -/
theorem integral_exp_neg (G : ℝ → ℂ) :
    (∫ t in Ioo (0 : ℝ) 1, G t)=
      ∫ x in Ioi (0 : ℝ), Real.exp (-x) • G (Real.exp (-x)) := by
  rw [←image_exp_neg]
  simpa only [abs_neg,abs_of_pos (Real.exp_pos _)] using
    integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
      (fun x _ => (exp_neg_deriv x).hasDerivWithinAt) exp_neg_injective.injOn G

/-- The integrability equivalence prevents a totalized-integral shortcut. -/
theorem integrable_exp_neg (G : ℝ → ℂ) :
    IntegrableOn G (Ioo (0 : ℝ) 1) ↔
      IntegrableOn (fun x : ℝ => Real.exp (-x) • G (Real.exp (-x))) (Ioi (0 : ℝ)) := by
  rw [←image_exp_neg]
  simpa only [abs_neg,abs_of_pos (Real.exp_pos _)] using
    integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi
      (fun x _ => (exp_neg_deriv x).hasDerivWithinAt) exp_neg_injective.injOn G

lemma exp_neg_cpow (x : ℝ) (w : ℂ) :
    (Real.exp (-x) : ℂ)^w=Complex.exp (-(x : ℂ)*w) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_pos (-x)).ne'),
    ←Complex.ofReal_log (Real.exp_pos (-x)).le,Real.log_exp]
  simp only [Complex.ofReal_neg]

lemma jacobian_power (x : ℝ) (w : ℂ) :
    (Real.exp (-x) : ℂ)*(Real.exp (-x) : ℂ)^(w-1)=
      Complex.exp (-w*(x : ℂ)) := by
  rw [exp_neg_cpow,Complex.ofReal_exp,←Complex.exp_add]
  congr 1
  push_cast
  ring

def gaussKernel (a : ℝ) (z : ℂ) (x : ℝ) : ℂ :=
  (Complex.exp (-(a : ℂ)*(x : ℂ))-Complex.exp (-z*(x : ℂ)))/
    (1-(Real.exp (-x) : ℂ))

/-- Exact transformed kernel, including the exp(-x) Jacobian. -/
lemma jacobian_kernel (a : ℝ) (z : ℂ) (x : ℝ) :
    Real.exp (-x) • limitKernel a z (Real.exp (-x))=gaussKernel a z x := by
  change (Real.exp (-x) : ℂ)*limitKernel a z (Real.exp (-x))=gaussKernel a z x
  unfold limitKernel powerDiff gaussKernel
  rw [←mul_div_assoc,mul_sub,jacobian_power,jacobian_power]

/-- The full cancelled Beta-domain integral equals the actual Gauss integral. -/
theorem limitKernel_integral (a : ℝ) (z : ℂ) :
    (∫ t in Ioo (0 : ℝ) 1, limitKernel a z t)=
      ∫ x in Ioi (0 : ℝ), gaussKernel a z x := by
  rw [integral_exp_neg]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (jacobian_kernel a z)

end DigammaGauss.Substitution
end -- close the source module noncomputable section
#print axioms DigammaGauss.Substitution.integral_exp_neg
#print axioms DigammaGauss.Substitution.integrable_exp_neg
#print axioms DigammaGauss.Substitution.jacobian_kernel
#print axioms DigammaGauss.Substitution.limitKernel_integral

/-! ## Extracted from RhWeilGaussRatio001.lean -/
/-! The actual Gamma-ratio side of the cancelled Beta limit. Every
nonvanishing and derivative premise is discharged in the positive half-plane.
No integral-limit or explicit-formula hypothesis is imported. -/
set_option maxHeartbeats 1000000
noncomputable section
open Set Filter Complex
open scoped Topology
namespace DigammaGauss.GammaRatio

/-- The difference vanishes at zero before multiplication by the Gamma pole. -/
def ratioDifference (a z h : ℂ) : ℂ :=
  Gamma a/Gamma (a+h)-Gamma z/Gamma (z+h)

lemma positive_not_pole {a : ℂ} (ha : 0<a.re) : ∀m:ℕ,a≠-(m:ℂ) := by
  intro m hm
  have hr := congrArg Complex.re hm
  norm_num at hr
  have hm0 : 0≤(m:ℝ) := Nat.cast_nonneg m
  linarith

lemma gamma_ratio_zero {a : ℂ} (ha : 0<a.re) : Gamma a/Gamma (a+0)=1 := by
  simp only [add_zero,div_self (Gamma_ne_zero_of_re_pos ha)]

lemma gamma_ratio_hasDerivAt {a : ℂ} (ha : 0<a.re) :
    HasDerivAt (fun h:ℂ=>Gamma a/Gamma (a+h)) (-digamma a) 0 := by
  have hg : Gamma a≠0 := Gamma_ne_zero_of_re_pos ha
  have hdG : HasDerivAt Gamma (deriv Gamma a) (a+(0:ℂ)) := by
    simpa only [add_zero] using
      (differentiableAt_Gamma a (positive_not_pole ha)).hasDerivAt
  have hG : HasDerivAt (fun h:ℂ=>Gamma (a+h)) (deriv Gamma a) 0 :=
    hdG.comp_const_add a 0
  have hq := (hasDerivAt_const (0:ℂ) (Gamma a)).div hG (by simpa using hg)
  convert hq using 1
  simp only [add_zero,zero_mul,zero_sub]
  rw [digamma_def,logDeriv_apply]
  field_simp [hg]
  <;> ring

@[simp] lemma ratioDifference_zero {a z : ℂ} (ha : 0<a.re) (hz : 0<z.re) :
    ratioDifference a z 0=0 := by
  rw [ratioDifference,gamma_ratio_zero ha,gamma_ratio_zero hz,sub_self]

lemma ratioDifference_hasDerivAt {a z : ℂ} (ha : 0<a.re) (hz : 0<z.re) :
    HasDerivAt (ratioDifference a z) (digamma z-digamma a) 0 := by
  have hd := (gamma_ratio_hasDerivAt ha).sub (gamma_ratio_hasDerivAt hz)
  unfold ratioDifference
  convert hd using 1 <;> ring

lemma ratioDifference_slope_limit {a z : ℂ} (ha : 0<a.re) (hz : 0<z.re) :
    Tendsto (fun h:ℝ=>ratioDifference a z (h:ℂ)/(h:ℂ)) (𝓝[>] 0)
      (𝓝 (digamma z-digamma a)) := by
  have hr : HasDerivAt (fun h:ℝ=>ratioDifference a z (h:ℂ))
      (digamma z-digamma a) 0 := by
    simpa only [Complex.ofReal_zero] using
      (ratioDifference_hasDerivAt ha hz).comp_ofReal
  have hs := hr.tendsto_slope_zero_right
  apply hs.congr'
  filter_upwards [] with h
  simp only [zero_add,Complex.ofReal_zero,ratioDifference_zero ha hz,sub_zero,
    RCLike.real_smul_eq_coe_mul]
  change ((h⁻¹:ℝ):ℂ)*ratioDifference a z (h:ℂ)=ratioDifference a z (h:ℂ)/(h:ℂ)
  rw [Complex.ofReal_inv,div_eq_mul_inv,mul_comm]

lemma ofReal_tendsto_zero_right_ne :
    Tendsto (fun h:ℝ=>(h:ℂ)) (𝓝[>] 0) (𝓝[≠] (0:ℂ)) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · simpa only [Complex.ofReal_zero] using
      (Complex.continuous_ofReal.tendsto (0:ℝ)).mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with h (hh:0<h)
    simpa only [mem_compl_iff,mem_singleton_iff,Complex.ofReal_eq_zero] using hh.ne'

lemma gamma_times_ratio_limit {a z : ℂ} (ha : 0<a.re) (hz : 0<z.re) :
    Tendsto (fun h:ℝ=>Gamma (h:ℂ)*ratioDifference a z (h:ℂ)) (𝓝[>] 0)
      (𝓝 (digamma z-digamma a)) := by
  have hp := tendsto_self_mul_Gamma_nhds_zero.comp ofReal_tendsto_zero_right_ne
  have hprod := hp.mul (ratioDifference_slope_limit ha hz)
  simp only [one_mul] at hprod
  apply hprod.congr'
  filter_upwards [self_mem_nhdsWithin] with h (hh:0<h)
  have hh0 : (h:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hh.ne'
  dsimp only [Function.comp_def]
  field_simp [hh0]
  <;> ring

lemma beta_difference_identity {a z : ℂ} (ha : 0<a.re) (hz : 0<z.re)
    {h : ℝ} (hh : 0<h) :
    betaIntegral a (h:ℂ)-betaIntegral z (h:ℂ)=
      Gamma (h:ℂ)*ratioDifference a z (h:ℂ) := by
  have hhc : 0<(h:ℂ).re := hh
  have hga : Gamma (a+(h:ℂ))≠0 :=
    Gamma_ne_zero_of_re_pos (by simpa only [add_re,ofReal_re] using add_pos ha hh)
  have hgz : Gamma (z+(h:ℂ))≠0 :=
    Gamma_ne_zero_of_re_pos (by simpa only [add_re,ofReal_re] using add_pos hz hh)
  have hba : betaIntegral a (h:ℂ)=Gamma a*Gamma (h:ℂ)/Gamma (a+(h:ℂ)) := by
    apply (eq_div_iff hga).mpr
    simpa only [mul_comm] using (Gamma_mul_Gamma_eq_betaIntegral ha hhc).symm
  have hbz : betaIntegral z (h:ℂ)=Gamma z*Gamma (h:ℂ)/Gamma (z+(h:ℂ)) := by
    apply (eq_div_iff hgz).mpr
    simpa only [mul_comm] using (Gamma_mul_Gamma_eq_betaIntegral hz hhc).symm
  rw [hba,hbz]
  unfold ratioDifference
  ring

/-- Actual cancelled Beta integrals have the digamma difference as their
right limit. The separate integral/DCT argument must identify that limit
with the Gauss integral before claiming Gauss' representation. -/
theorem beta_difference_limit_complex {a z : ℂ} (ha : 0<a.re) (hz : 0<z.re) :
    Tendsto (fun h:ℝ=>betaIntegral a (h:ℂ)-betaIntegral z (h:ℂ)) (𝓝[>] 0)
      (𝓝 (digamma z-digamma a)) := by
  apply (gamma_times_ratio_limit ha hz).congr'
  filter_upwards [self_mem_nhdsWithin] with h (hh:0<h)
  exact (beta_difference_identity ha hz hh).symm

theorem beta_difference_limit {a : ℝ} {z : ℂ} (ha : 0<a) (hz : 0<z.re) :
    Tendsto (fun h:ℝ=>betaIntegral (a:ℂ) (h:ℂ)-betaIntegral z (h:ℂ)) (𝓝[>] 0)
      (𝓝 (digamma z-digamma (a:ℂ))) :=
  beta_difference_limit_complex ha hz

end DigammaGauss.GammaRatio
end -- close the source module noncomputable section
#print axioms DigammaGauss.GammaRatio.gamma_ratio_hasDerivAt
#print axioms DigammaGauss.GammaRatio.ratioDifference_hasDerivAt
#print axioms DigammaGauss.GammaRatio.ratioDifference_slope_limit
#print axioms DigammaGauss.GammaRatio.gamma_times_ratio_limit
#print axioms DigammaGauss.GammaRatio.beta_difference_identity
#print axioms DigammaGauss.GammaRatio.beta_difference_limit_complex
#print axioms DigammaGauss.GammaRatio.beta_difference_limit

/-! ## Extracted from RhWeilGaussDifference001.lean -/
/-! The direct Gauss digamma-difference theorem, derived from the actual
Beta difference, its cancelled dominated limit, and exact logarithmic substitution.
No locally uniform Gamma-sequence differentiation or explicit formula is assumed. -/
set_option maxHeartbeats 0
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace DigammaGauss
open DigammaGauss.BetaDomination DigammaGauss.BetaLimit DigammaGauss.Substitution

/-- Equality of the two actual Beta-difference limits. -/
theorem beta_domain_digamma {a : ℝ} {z : ℂ} (ha : 0<a) (hz : 0<z.re) :
    Complex.digamma z-Complex.digamma (a : ℂ)=
      ∫ t in Ioo (0 : ℝ) 1, limitKernel a z t :=
  tendsto_nhds_unique (DigammaGauss.GammaRatio.beta_difference_limit ha hz)
    (beta_difference_integral_limit ha hz)

/-- The actual Gauss integrand is integrable on the whole positive half-line. -/
theorem gauss_integrable {a : ℝ} {z : ℂ} (ha : 0<a) (hz : 0<z.re) :
    IntegrableOn (gaussKernel a z) (Ioi (0 : ℝ)) := by
  have h := (integrable_exp_neg (limitKernel a z)).mp (limitKernel_integrable ha hz)
  apply h.congr
  exact Eventually.of_forall (jacobian_kernel a z)

/-- Gauss's exact difference formula for every real a>0 and complex Re(z)>0. -/
theorem digamma_difference {a : ℝ} {z : ℂ} (ha : 0<a) (hz : 0<z.re) :
    Complex.digamma z-Complex.digamma (a : ℂ)=
      ∫ x in Ioi (0 : ℝ), gaussKernel a z x := by
  rw [beta_domain_digamma ha hz,limitKernel_integral]

/-- The same theorem with the positive-real exponential written explicitly. -/
theorem digamma_difference_exp {a : ℝ} {z : ℂ} (ha : 0<a) (hz : 0<z.re) :
    Complex.digamma z-Complex.digamma (a : ℂ)=
      ∫ x in Ioi (0 : ℝ),
        ((Real.exp (-a*x) : ℂ)-Complex.exp (-z*(x : ℂ)))/(1-(Real.exp (-x) : ℂ)) := by
  rw [digamma_difference ha hz]
  apply integral_congr_ae
  exact Eventually.of_forall (fun x => by
    unfold gaussKernel
    rw [Complex.ofReal_exp]
    push_cast
    rfl)

/-- The explicit exponential integrand is integrable on the positive half-line.
This prevents an equality of totalized integrals from concealing divergence. -/
theorem gauss_integrable_exp {a : ℝ} {z : ℂ} (ha : 0<a) (hz : 0<z.re) :
    IntegrableOn (fun x : ℝ =>
      ((Real.exp (-a*x) : ℂ)-Complex.exp (-z*(x : ℂ)))/(1-(Real.exp (-x) : ℂ)))
      (Ioi (0 : ℝ)) := by
  apply (gauss_integrable ha hz).congr
  exact Eventually.of_forall (fun x => by
    unfold gaussKernel
    rw [Complex.ofReal_exp]
    push_cast
    rfl)

end DigammaGauss
end -- close the source module noncomputable section
#check @DigammaGauss.digamma_difference
#print axioms DigammaGauss.beta_domain_digamma
#print axioms DigammaGauss.gauss_integrable
#print axioms DigammaGauss.digamma_difference
#print axioms DigammaGauss.digamma_difference_exp

#print axioms DigammaGauss.gauss_integrable_exp
