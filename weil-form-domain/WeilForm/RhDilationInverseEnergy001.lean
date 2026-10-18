import RhDilationContraction001

/-! Inward native energy budget, deduced from the actual outward five-log
comparison and exact inverse dilation. Every infinite comparison uses the
existing full-energy theorem; no unproved finite-energy premise is hidden. -/
noncomputable section
open Set MeasureTheory Filter FourierTransform
open scoped Topology ENNReal
namespace RhDilationInverseEnergy
open RhDilation RhTail RhDilationContraction

lemma complexDilate_inverse_cancel {r : ℝ} (hr : 0 < r) (f : ℝ → ℂ) :
    complexDilate r (complexDilate r⁻¹ f) = f := by
  funext t
  have hs : Real.sqrt r ≠ 0 := (Real.sqrt_pos.mpr hr).ne'
  have ht : t / r / r⁻¹ = t := by field_simp
  simp only [complexDilate, Real.sqrt_inv, inv_inv, ht]
  have hc : (Real.sqrt r)⁻¹ * Real.sqrt r = 1 := inv_mul_cancel₀ hs
  rw [← mul_assoc, ← Complex.ofReal_mul, hc]
  simp

lemma complexDilate_inverse_cancel_left {r : ℝ} (hr : 0 < r) (f : ℝ → ℂ) :
    complexDilate r⁻¹ (complexDilate r f) = f := by
  simpa only [inv_inv] using complexDilate_inverse_cancel (inv_pos.mpr hr) f

lemma complexDilate_square_integral {r : ℝ} (hr : 0 < r) (f : ℝ → ℂ) :
    (∫ t, ‖complexDilate r f t‖ ^ 2) = ∫ t, ‖f t‖ ^ 2 := by
  simp_rw [complexDilate_norm_square hr]
  rw [integral_const_mul, Measure.integral_comp_div (fun t : ℝ => ‖f t‖ ^ 2) r,
    abs_of_pos hr]
  change r⁻¹ * (r * ∫ t, ‖f t‖ ^ 2) = _
  field_simp

/-- The reverse dilation has exactly the logarithmic native-energy payment. -/
theorem full_energy_inverse_bound {r b : ℝ} (hr : 1 ≤ r) (hb : 0 < b)
    {f : ℝ → ℂ} (hf : Integrable f volume) (h2 : MemLp f 2 volume) :
    fullFrequencyEnergy b
      ((complexDilate_memLp (inv_pos.mpr (by linarith : 0 < r)) hf h2).toLp
        (complexDilate r⁻¹ f)) ≤
      fullFrequencyEnergy b (h2.toLp f) +
        ENNReal.ofReal (((1 + 2 / b) * Real.log r) * ∫ t, ‖f t‖ ^ 2) := by
  have hrp : 0 < r := by linarith
  let g := complexDilate r⁻¹ f
  let hg1 := complexDilate_integrable (inv_pos.mpr hrp) hf
  let hg2 := complexDilate_memLp (inv_pos.mpr hrp) hf h2
  have heq : (complexDilate_memLp hrp hg1 hg2).toLp (complexDilate r g) = h2.toLp f := by
    apply Lp.ext
    filter_upwards [(complexDilate_memLp hrp hg1 hg2).coeFn_toLp, h2.coeFn_toLp]
      with t ht hft
    rw [ht, hft]
    exact congrFun (complexDilate_inverse_cancel hrp f) t
  have hs := full_energy_scaling hr hb hg1 hg2
  rw [heq] at hs
  change fullFrequencyEnergy b (hg2.toLp g) ≤ _
  have hm : (∫ t, ‖g t‖ ^ 2) = ∫ t, ‖f t‖ ^ 2 :=
    complexDilate_square_integral (inv_pos.mpr hrp) f
  rw [hm] at hs
  exact hs

end RhDilationInverseEnergy
#print axioms RhDilationInverseEnergy.complexDilate_inverse_cancel
#print axioms RhDilationInverseEnergy.complexDilate_inverse_cancel_left
#print axioms RhDilationInverseEnergy.full_energy_inverse_bound
