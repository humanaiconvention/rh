import RhSupportPrimeHinge001
import RhFinitePrimitiveIntegrability001
import RhFullKernelLimit001

set_option maxHeartbeats 0
noncomputable section
open Set MeasureTheory Filter
open scoped Topology BigOperators
namespace RhPrimeHingePrimitive
open RhAnchored RhSupportPrimeHinge

lemma primeHinge_as_difference (alpha L t u : ℝ) :
    primeHinge alpha L t u=finiteKernel 0 alpha L 0 t u-finiteKernel 0 0 L 0 t u := by
  unfold primeHinge finiteKernel anchoredKernel finitePotential
  simp only [Finset.sum_range_zero]
  ring

theorem physical_primitive_identity {R L : ℝ} (hR : 0<R) (hRL : R<L)
    {v : ℝ→ℝ} (hv : MemLp v 2 (physicalMeasure R)) (alpha : ℝ) :
    kernelQuadratic R (primeHinge alpha L) v=
      -alpha*(∫t in interval R,primeShift R L (primitive R v) t*primitive R v t) := by
  have hrowA (t : ℝ) : IntegrableOn
      (fun u => finiteKernel 0 alpha L 0 t u*v u*v t) (interval R) :=
    (finiteKernel_row_integrable hR hv 0 alpha L 0 t).mul_const _
  have hrow0 (t : ℝ) : IntegrableOn
      (fun u => finiteKernel 0 0 L 0 t u*v u*v t) (interval R) :=
    (finiteKernel_row_integrable hR hv 0 0 L 0 t).mul_const _
  have houterA := finiteKernel_outer_integrable hR hRL hv 0 alpha 0
  have houter0 := finiteKernel_outer_integrable hR hRL hv 0 0 0
  have hdiff : kernelQuadratic R (primeHinge alpha L) v=
      kernelQuadratic R (finiteKernel 0 alpha L 0) v-
        kernelQuadratic R (finiteKernel 0 0 L 0) v := by
    unfold kernelQuadratic
    rw [← integral_sub houterA houter0]
    apply integral_congr_ae
    exact Eventually.of_forall (fun t => by
      dsimp only
      rw [← integral_sub (hrowA t) (hrow0 t)]
      apply integral_congr_ae
      exact Eventually.of_forall (fun u => by
        dsimp only
        rw [primeHinge_as_difference]
        ring))
  have hA := finite_J_Schur_identity hR hRL hv 0 alpha 0
  have h0 := finite_J_Schur_identity hR hRL hv 0 0 0
  have hiA := native_quadratic_integrable hR hRL hv 0 alpha 0
  have hi0 := native_quadratic_integrable hR hRL hv 0 0 0
  rw [hdiff]
  change (∫t in interval R,∫u in interval R,finiteKernel 0 alpha L 0 t u*v u*v t)-
    (∫t in interval R,∫u in interval R,finiteKernel 0 0 L 0 t u*v u*v t)=_
  rw [hA,h0,← integral_sub hiA hi0,← integral_const_mul]
  apply integral_congr_ae
  exact Eventually.of_forall (fun t => by
    dsimp only
    unfold nativeOperator
    ring)

end RhPrimeHingePrimitive
#print axioms RhPrimeHingePrimitive.primeHinge_as_difference
#print axioms RhPrimeHingePrimitive.physical_primitive_identity
