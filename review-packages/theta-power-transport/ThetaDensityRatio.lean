import ThetaProbabilityMass

/-! Exact positive normalization scale for the actual theta/Macdonald
likelihood ratio; strict increase is inherited from the complete source. -/
noncomputable section
open Set
namespace ThetaMacdonald.Crossing
open Density Mass

def ratioScale : ℝ := macdonaldK0 (2*Real.pi)/(2*gamma0)
def likelihoodRatio (u : ℝ) : ℝ := ratioScale*Complete.ratio u

theorem ratioScale_pos : 0 < ratioScale :=
  div_pos (macdonaldK0_pos (mul_pos (by norm_num) Real.pi_pos))
    (mul_pos (by norm_num) gamma0_pos)

theorem likelihoodRatio_eq_density_div (u : ℝ) :
    likelihoodRatio u = thetaDensity u/macdonaldDensity u := by
  have hγ := gamma0_pos.ne'
  have hK : macdonaldK0 (2*Real.pi) ≠ 0 :=
    (macdonaldK0_pos (mul_pos (by norm_num) Real.pi_pos)).ne'
  unfold likelihoodRatio ratioScale Complete.ratio thetaDensity thetaProfile
    macdonaldDensity macdonaldKernel
  rw [referenceWeight_eq_cosh, neg_mul, Real.exp_neg]
  field_simp
  <;> ring

theorem continuous_likelihoodRatio : Continuous likelihoodRatio := by
  have hc : Continuous Complete.ratio :=
    continuous_iff_continuousAt.mpr (fun u => (Complete.hasDerivAt_ratio u).continuousAt)
  exact continuous_const.mul hc

theorem strictMonoOn_likelihoodRatio :
    StrictMonoOn likelihoodRatio (Ici (0 : ℝ)) := by
  intro u hu v hv huv
  exact mul_lt_mul_of_pos_left
    (Monotonicity.strictMonoOn_ratio hu hv huv) ratioScale_pos

theorem ratio_lt_one_iff (u : ℝ) :
    likelihoodRatio u < 1 ↔ thetaDensity u < macdonaldDensity u := by
  rw [likelihoodRatio_eq_density_div, div_lt_one (macdonaldDensity_pos u)]

theorem one_lt_ratio_iff (u : ℝ) :
    1 < likelihoodRatio u ↔ macdonaldDensity u < thetaDensity u := by
  rw [likelihoodRatio_eq_density_div, one_lt_div (macdonaldDensity_pos u)]

theorem ratio_eq_one_iff (u : ℝ) :
    likelihoodRatio u = 1 ↔ thetaDensity u = macdonaldDensity u := by
  rw [likelihoodRatio_eq_density_div]
  exact div_eq_one_iff_eq (macdonaldDensity_pos u).ne'

end ThetaMacdonald.Crossing
#print axioms ThetaMacdonald.Crossing.ratioScale_pos
#print axioms ThetaMacdonald.Crossing.likelihoodRatio_eq_density_div
#print axioms ThetaMacdonald.Crossing.continuous_likelihoodRatio
#print axioms ThetaMacdonald.Crossing.strictMonoOn_likelihoodRatio
#print axioms ThetaMacdonald.Crossing.ratio_eq_one_iff
