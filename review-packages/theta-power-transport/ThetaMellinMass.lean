import ThetaSeedFTC
import RhWeilCompletedGrowth001

/-! Match the actual modified-theta Mellin definition of completed zeta
to the actual positive-index seed integral. The assigned zero at t=1 is
retained; the positive-half-line identity is never asserted at its endpoint. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology BigOperators FourierTransform
namespace ThetaMacdonald.Mass
open Symmetry Density RhWeilThetaGeometry

def logTheta (v : ℝ) : ℂ :=
  Real.exp (-v/4) • modif (Real.exp (-v))

theorem integrable_logTheta : Integrable logTheta := by
  obtain ⟨C, hC, p, hp, hh⟩ := RhWeilTheta.fePair_modif_head_bound
  have h := RhWeilCompletedGrowth.weighted_integrable hC.le hp hh (1/4 : ℂ)
  convert h using 1
  funext v
  dsimp [logTheta]
  congr 2
  norm_num
  ring

theorem logTheta_even (v : ℝ) : logTheta (-v) = logTheta v := by
  have hi := modif_inv (Real.exp_pos v)
  rw [one_div, ← Real.exp_neg, Real.rpow_def_of_pos (Real.exp_pos v),
    Real.log_exp] at hi
  have he : Real.exp (-v/4)*Real.exp (v*(1/2 : ℝ)) = Real.exp (v/4) := by
    rw [← Real.exp_add]
    congr 1
    ring
  simp only [logTheta, neg_neg, RCLike.real_smul_eq_coe_mul,
    RCLike.ofReal_eq_complex_ofReal]
  rw [hi, ← mul_assoc, ← Complex.ofReal_mul, he]

theorem seedTail_hurwitz (u : ℝ) :
    seedTail u = Real.exp (u/2)*
      (HurwitzZeta.evenKernel 0 (Real.exp (2*u))-1)/2 := by
  have hs := HurwitzZeta.hasSum_int_evenKernel (0 : ℝ) (Real.exp_pos (2*u))
  have hs' : HasSum (fun n : ℤ =>
      Real.exp (-Real.pi*Real.exp (2*u)*(n:ℝ)^2))
      (HurwitzZeta.evenKernel 0 (Real.exp (2*u))) := by
    convert hs using 1
    funext n
    simp only [add_zero]
    congr 1
    ring
  have ht : Reflection.fullTheta u =
      HurwitzZeta.evenKernel 0 (Real.exp (2*u)) := hs'.tsum_eq
  calc
    seedTail u = (centeredTheta u - Real.exp (u/2))/2 := by
      dsimp [seedTail, centeredTheta]
      ring
    _ = _ := by
      rw [centeredTheta_eq_full]
      unfold Reflection.centeredFullTheta
      rw [ht]
      ring

theorem logTheta_neg_of_pos {v : ℝ} (hv : 0 < v) :
    logTheta (-v) = ((2*seedTail (v/2) : ℝ) : ℂ) := by
  have ht : 1 < Real.exp v := Real.one_lt_exp_iff.mpr hv
  have hb : modif (Real.exp v) =
      (HurwitzZeta.evenKernel 0 (Real.exp v) : ℂ)-1 := by
    simp [modif, WeakFEPair.f_modif, HurwitzZeta.hurwitzEvenFEPair,
      ht, notMem_Ioo_of_ge ht.le]
  rw [logTheta, neg_neg, hb, seedTail_hurwitz]
  rw [show 2*(v/2) = v by ring, show (v/2)/2 = v/4 by ring]
  simp only [RCLike.real_smul_eq_coe_mul, RCLike.ofReal_eq_complex_ofReal]
  push_cast
  ring

theorem logTheta_pos {v : ℝ} (hv : 0 < v) :
    logTheta v = ((2*seedTail (v/2) : ℝ) : ℂ) :=
  (logTheta_even v).symm.trans (logTheta_neg_of_pos hv)

theorem logTheta_half_integral_re :
    (∫ v in Ioi (0 : ℝ), logTheta v).re =
      4*(∫ u in Ioi (0 : ℝ), seedTail u) := by
  have hr : (∫ v in Ioi (0 : ℝ), logTheta v).re =
      ∫ v in Ioi (0 : ℝ), (logTheta v).re := by
    simpa only [RCLike.re_eq_complex_re] using
      (integral_re integrable_logTheta.integrableOn).symm
  rw [hr]
  calc
    _ = ∫ v in Ioi (0 : ℝ), 2*seedTail (v/2) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro v hv
      change (logTheta v).re = 2*seedTail (v/2)
      rw [logTheta_pos hv]
      rfl
    _ = 2*(∫ v in Ioi (0 : ℝ), seedTail ((1/2 : ℝ)*v)) := by
      rw [integral_const_mul]
      congr 2
      funext v
      congr 1
      ring
    _ = _ := by
      rw [integral_comp_mul_left_Ioi seedTail 0 (by norm_num : (0 : ℝ)<1/2)]
      norm_num [smul_eq_mul]
      ring

theorem completed_half_log :
    completedRiemannZeta₀ (1/2 : ℂ) = (∫ v : ℝ, logTheta v)/2 := by
  change mellin modif ((1/2 : ℂ)/2)/2 = _
  rw [show (1/2 : ℂ)/2 = 1/4 by norm_num, mellin_eq_fourier]
  norm_num
  rw [Real.fourier_eq']
  simp only [inner_zero_right, mul_zero, Complex.ofReal_zero,
    zero_mul, Complex.exp_zero, one_smul]
  congr 2
  funext v
  dsimp [logTheta]
  congr 2
  norm_num
  ring

theorem completed_half_real :
    (completedRiemannZeta₀ (1/2 : ℂ)).re =
      4*(∫ u in Ioi (0 : ℝ), seedTail u) := by
  have hn := integral_comp_neg_Ioi (0 : ℝ) logTheta
  simp only [neg_zero] at hn
  have he : (∫ v in Iic (0 : ℝ), logTheta v) =
      ∫ v in Ioi (0 : ℝ), logTheta v := by
    rw [← hn]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro v _
    exact logTheta_even v
  have hs := intervalIntegral.integral_Iic_add_Ioi
    (b := (0 : ℝ)) integrable_logTheta.integrableOn integrable_logTheta.integrableOn
  rw [he] at hs
  rw [completed_half_log, ← hs]
  simp only [← two_mul, mul_div_cancel_left₀ _ (by norm_num : (2 : ℂ) ≠ 0)]
  exact logTheta_half_integral_re

/-- The actual arithmetic xi value, using the entire pole-removed completion.
This is Re(xiTwice(1/2))/2, not a renamed theta integral. -/
def gamma0 : ℝ :=
  (1+(1/2 : ℂ)*((1/2 : ℂ)-1)*completedRiemannZeta₀ (1/2 : ℂ)).re/2

theorem thetaMass_eq_gamma0 : thetaMass = gamma0 := by
  have hc := completed_half_real
  rw [thetaMass_improper_FTC]
  unfold gamma0
  norm_num [Complex.mul_re, Complex.mul_im, Complex.div_re]
  linarith

theorem gamma0_pos : 0 < gamma0 := by
  rw [← thetaMass_eq_gamma0]
  exact thetaMass_pos

end ThetaMacdonald.Mass
#print axioms ThetaMacdonald.Mass.integrable_logTheta
#print axioms ThetaMacdonald.Mass.logTheta_even
#print axioms ThetaMacdonald.Mass.logTheta_neg_of_pos
#print axioms ThetaMacdonald.Mass.completed_half_log
#print axioms ThetaMacdonald.Mass.completed_half_real
#print axioms ThetaMacdonald.Mass.thetaMass_eq_gamma0
#print axioms ThetaMacdonald.Mass.gamma0_pos
