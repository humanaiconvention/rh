import RhAllPrimeKernel001
import RhEndpointComplexReality001

noncomputable section
open Set MeasureTheory Filter
namespace RhAllPrime
open RhAnchored
lemma arithmetic_symmetric (N : ℕ) (t u : ℝ) :
    arithmeticKernel N t u=arithmeticKernel N u t := by
  unfold arithmeticKernel
  apply Finset.sum_congr rfl
  intro n hn
  rw [hinge_symmetric]

lemma complete_symmetric (N : ℕ) (t u : ℝ) :
    completeKernel N t u=completeKernel N u t := by
  rw [completeKernel,completeKernel,RhEndpointComplex.fullKernel_symmetric,arithmetic_symmetric]


end RhAllPrime
#print axioms RhAllPrime.complete_symmetric
