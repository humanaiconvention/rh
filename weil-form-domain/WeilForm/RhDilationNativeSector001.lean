import RhAllPrimeIntegrability001
import RhAllPrimeCutoff001
import RhEndpointParityShift001
import RhFullKernelLimit001
import RhSupportLocalization001

noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace RhDilationNative
open RhAnchored
lemma kernelQuadratic_add {R:ℝ} {K M:ℝ→ℝ→ℝ}
    (hK:Continuous (fun p:ℝ×ℝ=>K p.1 p.2))
    (hM:Continuous (fun p:ℝ×ℝ=>M p.1 p.2))
    {v:ℝ→ℝ} (hv:MemLp v 2 (physicalMeasure R)) :
    kernelQuadratic R (fun t u=>K t u+M t u) v=
      kernelQuadratic R K v+kernelQuadratic R M v := by
  have hiK:=RhSupportLocalization.kernel_joint_integrable K hK hv hv
  have hiM:=RhSupportLocalization.kernel_joint_integrable M hM hv hv
  have hi:Integrable (fun p:ℝ×ℝ=>(K p.1 p.2+M p.1 p.2)*v p.2*v p.1)
      ((physicalMeasure R).prod (physicalMeasure R)) := by
    convert hiK.add hiM using 1
    funext p
    dsimp only [Pi.add_apply]
    ring
  change (∫t,∫u,(K t u+M t u)*v u*v t ∂physicalMeasure R ∂physicalMeasure R)=_
  calc
    _ = ∫p:ℝ×ℝ,(K p.1 p.2+M p.1 p.2)*v p.2*v p.1 ∂((physicalMeasure R).prod (physicalMeasure R)) := (integral_prod _ hi).symm
    _=(∫p:ℝ×ℝ,K p.1 p.2*v p.2*v p.1 ∂((physicalMeasure R).prod (physicalMeasure R)))+
       (∫p:ℝ×ℝ,M p.1 p.2*v p.2*v p.1 ∂((physicalMeasure R).prod (physicalMeasure R))) := by
      rw[←integral_add hiK hiM]
      apply integral_congr_ae
      exact Eventually.of_forall (fun p=>by ring)
    _=_ := by rw[integral_prod _ hiK,integral_prod _ hiM];rfl


end RhDilationNative
#print axioms RhDilationNative.kernelQuadratic_add
