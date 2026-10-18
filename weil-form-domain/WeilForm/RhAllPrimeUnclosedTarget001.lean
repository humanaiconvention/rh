import RhFullKernelLimit001
import RhSupportLocalization001

noncomputable section
open Set MeasureTheory Filter
namespace RhAllPrimeTarget
open RhAnchored
def pair (R : ℝ) (K : ℝ→ℝ→ℝ) (f g : ℝ→ℝ) : ℝ :=
  ∫p : ℝ×ℝ,K p.1 p.2*f p.2*g p.1 ∂((physicalMeasure R).prod (physicalMeasure R))

lemma pair_self {R : ℝ} (K : ℝ→ℝ→ℝ)
    (hK : Continuous (fun p : ℝ×ℝ => K p.1 p.2)) {v : ℝ→ℝ}
    (hv : MemLp v 2 (physicalMeasure R)) : pair R K v v=kernelQuadratic R K v :=
  integral_prod _ (RhSupportLocalization.kernel_joint_integrable K hK hv hv)

lemma pair_add_first {R : ℝ} (K : ℝ→ℝ→ℝ)
    (hK : Continuous (fun p : ℝ×ℝ => K p.1 p.2)) {f g h : ℝ→ℝ}
    (hf : MemLp f 2 (physicalMeasure R)) (hg : MemLp g 2 (physicalMeasure R))
    (hh : MemLp h 2 (physicalMeasure R)) :
    pair R K (f+g) h=pair R K f h+pair R K g h := by
  unfold pair
  calc
    _ = ∫p : ℝ×ℝ,(K p.1 p.2*f p.2*h p.1+K p.1 p.2*g p.2*h p.1)
        ∂((physicalMeasure R).prod (physicalMeasure R)) := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun p => by dsimp only [Pi.add_apply];ring)
    _ = _ := integral_add (RhSupportLocalization.kernel_joint_integrable K hK hf hh)
      (RhSupportLocalization.kernel_joint_integrable K hK hg hh)

lemma pair_add_second {R : ℝ} (K : ℝ→ℝ→ℝ)
    (hK : Continuous (fun p : ℝ×ℝ => K p.1 p.2)) {f g h : ℝ→ℝ}
    (hf : MemLp f 2 (physicalMeasure R)) (hg : MemLp g 2 (physicalMeasure R))
    (hh : MemLp h 2 (physicalMeasure R)) :
    pair R K f (g+h)=pair R K f g+pair R K f h := by
  unfold pair
  calc
    _ = ∫p : ℝ×ℝ,(K p.1 p.2*f p.2*g p.1+K p.1 p.2*f p.2*h p.1)
        ∂((physicalMeasure R).prod (physicalMeasure R)) := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun p => by dsimp only [Pi.add_apply];ring)
    _ = _ := integral_add (RhSupportLocalization.kernel_joint_integrable K hK hf hg)
      (RhSupportLocalization.kernel_joint_integrable K hK hf hh)

lemma pair_symmetric (R : ℝ) (K : ℝ→ℝ→ℝ) (hSym : ∀t u,K t u=K u t)
    (f g : ℝ→ℝ) : pair R K f g=pair R K g f := by
  unfold pair
  calc
    _ = ∫p : ℝ×ℝ,K p.2 p.1*g p.1*f p.2
        ∂((physicalMeasure R).prod (physicalMeasure R)) := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun p => by change K p.1 p.2 * f p.2 * g p.1 = K p.2 p.1 * g p.1 * f p.2; rw [hSym p.2 p.1]; ring)
    _ = _ := integral_prod_swap (fun p : ℝ×ℝ=>K p.1 p.2*g p.2*f p.1)


end RhAllPrimeTarget
#print axioms RhAllPrimeTarget.pair_self
#print axioms RhAllPrimeTarget.pair_symmetric
