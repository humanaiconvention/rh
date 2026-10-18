import RhPrimitiveFormDomain001
import RhEndpointComplex001

/-!
The actual positive archimedean tail is represented by its own continuous,
globally bounded anchored kernel. This does not assume the complete arithmetic
form is positive and does not identify Suzuki's closed form domain.
-/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology BigOperators ENNReal
namespace RhNativeArchKernel
open RhAnchored RhTail

/-- Exactly the omitted native archimedean series, with no ranks or primes. -/
def energyKernel (t u : ℝ) : ℝ := - ∑' k : ℕ, archKernelTerm k t u

def bound : ℝ := ∑' k : ℕ, archMajorant k

lemma bound_nonnegative : 0 ≤ bound := tsum_nonneg archMajorant_nonneg

lemma kernel_eq_difference (C alpha L t u : ℝ) :
    energyKernel t u = fullKernel C alpha L t u - finiteKernel C alpha L 0 t u := by
  unfold energyKernel fullKernel
  ring

lemma kernel_continuous : Continuous (fun p : ℝ × ℝ => energyKernel p.1 p.2) := by
  have hf : Continuous (fun p : ℝ × ℝ => finiteKernel 0 0 0 0 p.1 p.2) := by
    unfold finiteKernel anchoredKernel finitePotential
    simp only [Finset.sum_range_zero]
    fun_prop
  have he : (fun p : ℝ × ℝ => energyKernel p.1 p.2) =
      (fun p : ℝ × ℝ => fullKernel 0 0 0 p.1 p.2 - finiteKernel 0 0 0 0 p.1 p.2) := by
    funext p
    exact kernel_eq_difference 0 0 0 p.1 p.2
  rw [he]
  exact (RhEndpointComplex.fullKernel_joint_continuous 0 0 0).sub hf

lemma kernel_zero_left (u : ℝ) : energyKernel 0 u = 0 := by
  simp only [energyKernel, archKernelTerm, anchoredKernel_zero_left, tsum_zero, neg_zero]

lemma kernel_zero_right (t : ℝ) : energyKernel t 0 = 0 := by
  simp only [energyKernel, archKernelTerm, anchoredKernel_zero_right, tsum_zero, neg_zero]

/-- The bound is global; no radius-dependent compact bound is needed. -/
lemma kernel_norm_le (t u : ℝ) : ‖energyKernel t u‖ ≤ bound := by
  unfold energyKernel bound
  rw [norm_neg]
  exact (norm_tsum_le_tsum_norm (archKernelTerm_summable t u).norm).trans
    ((archKernelTerm_summable t u).norm.tsum_le_tsum
      (fun k => archKernelTerm_norm_le k t u) archMajorant_summable)

lemma physical_difference {R : ℝ} (hR : 0 < R)
    {v : ℝ → ℝ} (hv : MemLp v 2 (physicalMeasure R)) :
    kernelQuadratic R energyKernel v = fullQuadratic R 0 0 (R + 1) v -
      finiteQuadratic R 0 0 (R + 1) 0 v := by
  have hRL : R < R + 1 := by linarith
  have houterF := fullKernel_outer_integrable hR hRL hv 0 0
  have houter0 := finiteKernel_outer_integrable hR hRL hv 0 0 0
  unfold fullQuadratic finiteQuadratic kernelQuadratic
  rw [← integral_sub houterF houter0]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  have hrowF := (fullKernel_row_integrable hR hv 0 0 (R + 1) ht).mul_const (v t)
  have hrow0 := (finiteKernel_row_integrable hR hv 0 0 (R + 1) 0 t).mul_const (v t)
  rw [← integral_sub hrowF hrow0]
  apply integral_congr_ae
  exact Eventually.of_forall (fun u => by
    dsimp only
    rw [kernel_eq_difference 0 0 (R + 1)]
    ring)

/-- Actual kernel identity for the whole positive Fourier energy, at every R>0. -/
theorem full_energy_identity {R : ℝ} (hR : 0 < R)
    {v : ℝ → ℝ} (hv : MemLp v 2 (physicalMeasure R)) :
    fullFrequencyEnergy (1 / 2)
      (physicalFourierVector R (primitive R v) (primitive_memLp hv)) =
      ENNReal.ofReal (kernelQuadratic R energyKernel v) := by
  have h := (physical_fourier_tail_limit hR (by linarith : R < R + 1) hv 0 0 0).1
  have hbeta : beta 0 = (1 / 2 : ℝ) := by norm_num [beta, archIndex]
  rw [hbeta, ← physical_difference hR hv] at h
  exact h

/-- Positivity here is only of the pure positive archimedean tail. -/
theorem kernel_quadratic_nonnegative {R : ℝ} (hR : 0 < R)
    {v : ℝ → ℝ} (hv : MemLp v 2 (physicalMeasure R)) :
    0 ≤ kernelQuadratic R energyKernel v := by
  rw [physical_difference hR hv]
  exact (physical_fourier_tail_limit hR (by linarith : R < R + 1) hv 0 0 0).2

lemma integrand_integrable {R : ℝ} {v : ℝ → ℝ}
    (hv : MemLp v 2 (physicalMeasure R)) :
    Integrable (fun p : ℝ × ℝ => energyKernel p.1 p.2 * v p.2 * v p.1)
      ((physicalMeasure R).prod (physicalMeasure R)) := by
  have hv1 : Integrable v (physicalMeasure R) := hv.integrable (by norm_num)
  have hm : AEStronglyMeasurable
      (fun p : ℝ × ℝ => energyKernel p.1 p.2 * v p.2 * v p.1)
      ((physicalMeasure R).prod (physicalMeasure R)) :=
    (kernel_continuous.aestronglyMeasurable.mul
      hv.aestronglyMeasurable.comp_snd).mul hv.aestronglyMeasurable.comp_fst
  apply ((hv1.norm.mul_prod hv1.norm).const_mul bound).mono' hm
  exact Eventually.of_forall (fun p => by
    rw [norm_mul, norm_mul]
    have h := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (kernel_norm_le p.1 p.2) (norm_nonneg (v p.2)))
      (norm_nonneg (v p.1))
    nlinarith)

/-- Exact quantitative control of the native energy by physical L1 mass. -/
theorem kernel_quadratic_norm_bound {R : ℝ} {v : ℝ → ℝ}
    (hv : MemLp v 2 (physicalMeasure R)) :
    ‖kernelQuadratic R energyKernel v‖ ≤ bound * (∫ t in interval R, ‖v t‖) ^ 2 := by
  have hv1 : Integrable v (physicalMeasure R) := hv.integrable (by norm_num)
  have hi := integrand_integrable hv
  have he : kernelQuadratic R energyKernel v =
      ∫ p : ℝ × ℝ, energyKernel p.1 p.2 * v p.2 * v p.1
        ∂((physicalMeasure R).prod (physicalMeasure R)) := by
    exact (integral_prod _ hi).symm
  rw [he]
  calc
    _ ≤ ∫ p : ℝ × ℝ, ‖energyKernel p.1 p.2 * v p.2 * v p.1‖
        ∂((physicalMeasure R).prod (physicalMeasure R)) := norm_integral_le_integral_norm _
    _ ≤ ∫ p : ℝ × ℝ, bound * (‖v p.1‖ * ‖v p.2‖)
        ∂((physicalMeasure R).prod (physicalMeasure R)) := by
      apply integral_mono hi.norm ((hv1.norm.mul_prod hv1.norm).const_mul bound)
      intro p
      dsimp only
      rw [norm_mul, norm_mul]
      have h := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (kernel_norm_le p.1 p.2) (norm_nonneg (v p.2)))
        (norm_nonneg (v p.1))
      nlinarith
    _ = _ := by
      rw [integral_const_mul]
      have hp := integral_prod_mul (μ := physicalMeasure R) (ν := physicalMeasure R)
        (fun t : ℝ => ‖v t‖) (fun t : ℝ => ‖v t‖)
      rw [hp]
      simp only [physicalMeasure, pow_two]

end RhNativeArchKernel
#print axioms RhNativeArchKernel.kernel_continuous
#print axioms RhNativeArchKernel.kernel_zero_left
#print axioms RhNativeArchKernel.kernel_norm_le
#print axioms RhNativeArchKernel.full_energy_identity
#print axioms RhNativeArchKernel.kernel_quadratic_nonnegative
#print axioms RhNativeArchKernel.kernel_quadratic_norm_bound
