import ThetaMellinMass

/-! The source gamma0 is the actual arithmetic xi value. Unit mass follows
for the originally stated density, without changing its normalizer. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace ThetaMacdonald.Mass
open Density RhWeilThetaGeometry

/-- Classical xi at s=1/2, with the actual standard Riemann zeta function.
Gammaℝ s is pi^(-s/2)*Gamma(s/2), using mathlib's fixed convention. -/
def xiHalf : ℂ :=
  ((1/2 : ℂ)*((1/2 : ℂ)-1)*Complex.Gammaℝ (1/2 : ℂ)*
    riemannZeta (1/2 : ℂ))/2

theorem xiHalf_eq_entire :
    xiHalf =
      (1+(1/2 : ℂ)*((1/2 : ℂ)-1)*completedRiemannZeta₀ (1/2 : ℂ))/2 := by
  have hg : Complex.Gammaℝ (1/2 : ℂ) ≠ 0 :=
    Complex.Gammaℝ_ne_zero_of_re_pos (by norm_num)
  unfold xiHalf
  rw [riemannZeta_def_of_ne_zero (by norm_num : (1/2 : ℂ) ≠ 0)]
  calc
    _ = ((1/2 : ℂ)*((1/2 : ℂ)-1)*completedRiemannZeta (1/2 : ℂ))/2 := by
      field_simp
    _ = _ := by
      rw [completedRiemannZeta_eq]
      norm_num
      ring

theorem logTheta_im_zero (v : ℝ) : (logTheta v).im = 0 := by
  rcases lt_trichotomy v 0 with hv | rfl | hv
  · rw [← logTheta_even v, logTheta_pos (neg_pos.mpr hv)]
    rfl
  · simp [logTheta, modif_one]
  · rw [logTheta_pos hv]
    rfl

theorem completed_half_im_zero :
    (completedRiemannZeta₀ (1/2 : ℂ)).im = 0 := by
  have hi : (∫ v : ℝ, logTheta v).im = ∫ v : ℝ, (logTheta v).im := by
    simpa only [RCLike.im_eq_complex_im] using
      (integral_im integrable_logTheta).symm
  rw [completed_half_log]
  simp [Complex.div_im, hi, logTheta_im_zero]

theorem xiHalf_eq_gamma0 : xiHalf = (gamma0 : ℂ) := by
  rw [xiHalf_eq_entire]
  apply Complex.ext
  · simp [gamma0, Complex.div_re]
  · norm_num [Complex.div_im, Complex.mul_im, Complex.mul_re, completed_half_im_zero]

/-- The exact original complex normalization; no Re projection remains. -/
theorem thetaMass_eq_xiHalf : (thetaMass : ℂ) = xiHalf := by
  rw [thetaMass_eq_gamma0, xiHalf_eq_gamma0]

def thetaDensity (u : ℝ) : ℝ := thetaProfile u/gamma0

theorem integrable_thetaDensity :
    IntegrableOn thetaDensity (Ioi (0 : ℝ)) :=
  integrable_thetaProfile.div_const gamma0

theorem thetaDensity_pos {u : ℝ} (hu : 0 ≤ u) :
    0 < thetaDensity u :=
  div_pos (thetaProfile_pos hu) gamma0_pos

theorem thetaDensity_mass :
    (∫ u in Ioi (0 : ℝ), thetaDensity u) = 1 := by
  unfold thetaDensity
  simp only [div_eq_mul_inv]
  rw [integral_mul_const]
  change thetaMass*gamma0⁻¹ = 1
  rw [thetaMass_eq_gamma0, mul_inv_cancel₀ gamma0_pos.ne']

theorem thetaDensity_mass_closed :
    (∫ u in Ici (0 : ℝ), thetaDensity u) = 1 := by
  rw [integral_Ici_eq_integral_Ioi, thetaDensity_mass]

theorem actual_equal_probability_masses :
    (∫ u in Ici (0 : ℝ), thetaDensity u) =
      ∫ u in Ici (0 : ℝ), macdonaldDensity u := by
  rw [thetaDensity_mass_closed, macdonaldDensity_mass_closed]

end ThetaMacdonald.Mass
#print axioms ThetaMacdonald.Mass.xiHalf_eq_entire
#print axioms ThetaMacdonald.Mass.completed_half_im_zero
#print axioms ThetaMacdonald.Mass.xiHalf_eq_gamma0
#print axioms ThetaMacdonald.Mass.thetaMass_eq_xiHalf
#print axioms ThetaMacdonald.Mass.integrable_thetaDensity
#print axioms ThetaMacdonald.Mass.thetaDensity_pos
#print axioms ThetaMacdonald.Mass.thetaDensity_mass
#print axioms ThetaMacdonald.Mass.thetaDensity_mass_closed
#print axioms ThetaMacdonald.Mass.actual_equal_probability_masses
