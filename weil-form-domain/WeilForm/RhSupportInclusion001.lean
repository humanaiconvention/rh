import RhFullKernelLimit001

noncomputable section
open Set MeasureTheory Filter
open scoped ComplexConjugate
namespace RhSupport
open RhAnchored
def complexEnergy (R : ℝ) (K : ℝ→ℝ→ℝ) (v : ℝ→ℂ) : ℂ :=
  ∫t in interval R,∫u in interval R,(K t u : ℂ)*conj (v t)*v u


end RhSupport
#print axioms RhSupport.complexEnergy
