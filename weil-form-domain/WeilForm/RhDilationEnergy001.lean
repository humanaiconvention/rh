import RhDilationFrequency001

noncomputable section
open Set MeasureTheory Filter FourierTransform
open scoped Topology BigOperators ENNReal
namespace RhDilation
open RhTail

/-- The finite comparisons pass to the full nonnegative multiplier by the
proved monotone Fourier-tail convergence, with its finite norm budget. -/
theorem full_energy_scaling {r b:ℝ} (hr:1≤r) (hb:0<b)
    {f:ℝ→ℂ} (hf:Integrable f volume) (h2:MemLp f 2 volume) :
    fullFrequencyEnergy b (h2.toLp f) ≤
      fullFrequencyEnergy b ((complexDilate_memLp (by linarith:0<r) hf h2).toLp (complexDilate r f))+
      ENNReal.ofReal (((1+2/b)*Real.log r)*(∫t:ℝ,‖f t‖^2)) := by
  have hrp:0<r:=by linarith
  let hg1:=complexDilate_integrable hrp hf
  let hg2:=complexDilate_memLp hrp hf h2
  have hbudget:0≤((1+2/b)*Real.log r)*(∫t:ℝ,‖f t‖^2) :=
    mul_nonneg (mul_nonneg (by positivity) (Real.log_nonneg hr))
      (integral_nonneg (fun t=>sq_nonneg _))
  have hfK:=frequency_tail_limit hb (h2.toLp f)
  have hgK: Tendsto (fun K=>finiteFrequencyEnergy b (hg2.toLp (complexDilate r f)) K+
      ENNReal.ofReal (((1+2/b)*Real.log r)*(∫t:ℝ,‖f t‖^2))) atTop
      (𝓝 (fullFrequencyEnergy b (hg2.toLp (complexDilate r f))+
      ENNReal.ofReal (((1+2/b)*Real.log r)*(∫t:ℝ,‖f t‖^2)))) :=
    (frequency_tail_limit hb (hg2.toLp (complexDilate r f))).add_const _
  apply le_of_tendsto_of_tendsto hfK hgK
  apply Eventually.of_forall
  intro K
  dsimp only
  have hn : 0≤∫ξ:ℝ,finiteMultiplier b K (2*Real.pi*ξ)*rawDensity (complexDilate r f) ξ :=
    integral_nonneg (fun ξ=>mul_nonneg (finiteMultiplier_nonneg hb K _) (sq_nonneg _))
  rw [finite_energy_frequency hb hf h2,finite_energy_frequency hb hg1 hg2,
    ←ENNReal.ofReal_add hn hbudget]
  exact ENNReal.ofReal_le_ofReal (finite_energy_scaling hr hb hf h2 K)

end RhDilation
#print axioms RhDilation.full_energy_scaling


