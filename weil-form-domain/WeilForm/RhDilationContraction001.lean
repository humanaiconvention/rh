import RhDilationEnergy001
import RhWeightedEnergyIdentity001

/-! Outward contraction of the actual complete native positive energy.
Finite signed multiplier comparisons pass to the existing monotone tail limit;
no infinite sum/integral exchange is introduced. -/
noncomputable section
open Set MeasureTheory Filter FourierTransform
open scoped Topology BigOperators ENNReal
namespace RhDilationContraction
open RhDilation RhTail RhWeightedEnergyIdentity

lemma finite_energy_contraction {r b : ℝ} (hr : 1 ≤ r) (hb : 0 < b)
    {f : ℝ → ℂ} (hf : Integrable f volume) (h2 : MemLp f 2 volume) (K : ℕ) :
    (∫ xi, finiteMultiplier b K (2 * Real.pi * xi) * rawDensity (complexDilate r f) xi) ≤
      ∫ xi, finiteMultiplier b K (2 * Real.pi * xi) * rawDensity f xi := by
  have hrp : 0 < r := by linarith
  rw [finite_energy_dilate hrp]
  have hi0 := finite_density_integrable hf h2 hb K 1
  simp only [div_one] at hi0
  have hi1 := finite_density_integrable hf h2 hb K r
  apply integral_mono hi1 hi0
  intro xi
  have hm := (RhDilationScalar.finite_multiplier_scaling hb hr (2 * Real.pi * xi) K).1
  have hd : 0 ≤ rawDensity f xi := sq_nonneg _
  unfold finiteMultiplier at *
  exact mul_le_mul_of_nonneg_right (sub_nonneg.mp hm) hd

/-- The actual full ENNReal comparison is proved before finiteness conversion. -/
theorem full_energy_contraction {r b : ℝ} (hr : 1 ≤ r) (hb : 0 < b)
    {f : ℝ → ℂ} (hf : Integrable f volume) (h2 : MemLp f 2 volume) :
    fullFrequencyEnergy b
      ((complexDilate_memLp (by linarith : 0 < r) hf h2).toLp (complexDilate r f)) ≤
      fullFrequencyEnergy b (h2.toLp f) := by
  have hrp : 0 < r := by linarith
  let hg1 := complexDilate_integrable hrp hf
  let hg2 := complexDilate_memLp hrp hf h2
  apply le_of_tendsto_of_tendsto (frequency_tail_limit hb (hg2.toLp (complexDilate r f)))
    (frequency_tail_limit hb (h2.toLp f))
  apply Eventually.of_forall
  intro K
  rw [finite_energy_frequency hb hg1 hg2, finite_energy_frequency hb hf h2]
  exact ENNReal.ofReal_le_ofReal (finite_energy_contraction hr hb hf h2 K)

lemma complexDilate_norm_square {r : ℝ} (hr : 0 < r) (f : ℝ → ℂ) (t : ℝ) :
    ‖complexDilate r f t‖ ^ 2 = r⁻¹ * ‖f (t / r)‖ ^ 2 := by
  simp only [complexDilate, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow,
    sq_abs, inv_pow, Real.sq_sqrt hr.le]

/-- The spatial dilation keeps exactly the physical L2 mass. -/
theorem complexDilate_L2_norm_square {r : ℝ} (hr : 0 < r)
    {f : ℝ → ℂ} (hf : Integrable f volume) (h2 : MemLp f 2 volume) :
    ‖(complexDilate_memLp hr hf h2).toLp (complexDilate r f)‖ ^ 2 = ‖h2.toLp f‖ ^ 2 := by
  rw [lp_norm_sq_integral, lp_norm_sq_integral]
  calc
    _ = ∫ t, ‖complexDilate r f t‖ ^ 2 := by
      apply integral_congr_ae
      filter_upwards [(complexDilate_memLp hr hf h2).coeFn_toLp] with t ht
      rw [ht]
    _ = ∫ t, r⁻¹ * ‖f (t / r)‖ ^ 2 := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun t => complexDilate_norm_square hr f t)
    _ = r⁻¹ * (r * ∫ t, ‖f t‖ ^ 2) := by
      rw [integral_const_mul, Measure.integral_comp_div (fun t : ℝ => ‖f t‖ ^ 2) r,
        abs_of_pos hr]
      rfl
    _ = ∫ t, ‖f t‖ ^ 2 := by field_simp
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [h2.coeFn_toLp] with t ht
      rw [ht]

end RhDilationContraction
#print axioms RhDilationContraction.full_energy_contraction
#print axioms RhDilationContraction.complexDilate_L2_norm_square
