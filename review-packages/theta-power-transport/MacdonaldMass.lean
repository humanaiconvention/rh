import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Tactic

/-! Order-zero Macdonald function on positive real arguments, defined by its
classical integral representation (DLMF10.32.9). This is not an arbitrary
replacement normalizer. The pinned library has no existing K0 definition.
-/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace ThetaMacdonald.Density

def macdonaldKernel (x t : ℝ) : ℝ := Real.exp (-x * Real.cosh t)
def macdonaldK0 (x : ℝ) : ℝ := ∫ t in Ioi (0 : ℝ), macdonaldKernel x t
def macdonaldDensity (u : ℝ) : ℝ :=
  2 * macdonaldKernel (2 * Real.pi) (2*u) / macdonaldK0 (2 * Real.pi)

theorem cosh_lower_half {t : ℝ} (ht : 0 ≤ t) :
    t/2 ≤ Real.cosh t := by
  rw [Real.cosh_eq]
  have h := Real.add_one_le_exp t
  have hp := Real.exp_pos (-t)
  linarith

theorem integrable_macdonaldKernel {x : ℝ} (hx : 0 < x) :
    IntegrableOn (macdonaldKernel x) (Ioi (0 : ℝ)) := by
  have he := integrableOn_exp_mul_Ioi (a := -x/2) (by linarith) 0
  apply he.mono' (show AEStronglyMeasurable (macdonaldKernel x)
      (volume.restrict (Ioi (0 : ℝ))) from (by
        have hc : Continuous (macdonaldKernel x) := by unfold macdonaldKernel; fun_prop
        exact hc.aestronglyMeasurable))
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  change ‖Real.exp (-x * Real.cosh t)‖ ≤ Real.exp ((-x/2)*t)
  rw [Real.norm_of_nonneg (Real.exp_pos _).le]
  apply Real.exp_le_exp.mpr
  have h := mul_le_mul_of_nonneg_left (cosh_lower_half ht.le) hx.le
  nlinarith

theorem macdonaldK0_pos {x : ℝ} (hx : 0 < x) :
    0 < macdonaldK0 x := by
  have hnonneg : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] macdonaldKernel x :=
    Eventually.of_forall (fun t => (Real.exp_pos _).le)
  apply (setIntegral_pos_iff_support_of_nonneg_ae hnonneg
    (integrable_macdonaldKernel hx)).2
  have hs : Function.support (macdonaldKernel x) = univ := by
    ext t
    simp [Function.mem_support, macdonaldKernel, Real.exp_ne_zero]
  rw [hs, univ_inter]
  simp

theorem integrable_macdonaldDensity :
    IntegrableOn macdonaldDensity (Ioi (0 : ℝ)) := by
  have hx : 0 < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos
  have hc : IntegrableOn (fun u : ℝ => macdonaldKernel (2*Real.pi) (2*u))
      (Ioi (0 : ℝ)) :=
    (integrableOn_Ioi_comp_mul_left_iff (macdonaldKernel (2*Real.pi)) 0
      (by norm_num : (0 : ℝ) < 2)).2 (by
        simpa only [mul_zero] using integrable_macdonaldKernel hx)
  exact (hc.const_mul 2).div_const _

theorem macdonaldDensity_pos (u : ℝ) : 0 < macdonaldDensity u := by
  exact div_pos (mul_pos (by norm_num) (Real.exp_pos _))
    (macdonaldK0_pos (mul_pos (by norm_num) Real.pi_pos))

theorem macdonaldDensity_mass :
    (∫ u in Ioi (0 : ℝ), macdonaldDensity u) = 1 := by
  have hx : 0 < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos
  have hn := (macdonaldK0_pos hx).ne'
  unfold macdonaldDensity
  simp only [div_eq_mul_inv]
  rw [integral_mul_const, integral_const_mul,
    integral_comp_mul_left_Ioi (macdonaldKernel (2*Real.pi)) 0
      (by norm_num : (0 : ℝ) < 2)]
  simp only [mul_zero, smul_eq_mul]
  change (2 * ((2 : ℝ)⁻¹ * macdonaldK0 (2*Real.pi))) *
    (macdonaldK0 (2*Real.pi))⁻¹ = 1
  field_simp
  <;> simp_all

theorem macdonaldDensity_mass_closed :
    (∫ u in Ici (0 : ℝ), macdonaldDensity u) = 1 := by
  rw [integral_Ici_eq_integral_Ioi, macdonaldDensity_mass]

end ThetaMacdonald.Density
#print axioms ThetaMacdonald.Density.integrable_macdonaldKernel
#print axioms ThetaMacdonald.Density.macdonaldK0_pos
#print axioms ThetaMacdonald.Density.integrable_macdonaldDensity
#print axioms ThetaMacdonald.Density.macdonaldDensity_pos
#print axioms ThetaMacdonald.Density.macdonaldDensity_mass
#print axioms ThetaMacdonald.Density.macdonaldDensity_mass_closed
