import RhPhysicalTailLimit001

/-!
Only the complete ARCHIMEDEAN Fourier finite-energy prerequisite is proved here.
This is not equality with Suzuki's closed form domain and is not a smooth-core
approximation theorem. In particular it supplies no Schur inverse or positivity.
-/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace RhPrimitiveFormDomain

/-- Finite energy for the actual complete positive archimedean multiplier. -/
def FullArchFiniteEnergy (F : RhTail.WholeSpace) : Prop :=
  RhTail.fullFrequencyEnergy (1 / 2) F < ⊤

/-- Every actual physical anchored primitive has complete archimedean energy
at every finite positive radius, not only in the first-prime support window. -/
theorem physical_primitive_full_arch_finite {A : ℝ} (hA : 0 < A)
    {v : ℝ → ℝ} (hv : MemLp v 2 (RhAnchored.physicalMeasure A)) :
    FullArchFiniteEnergy
      (RhTail.physicalFourierVector A (RhAnchored.primitive A v)
        (RhAnchored.primitive_memLp hv)) := by
  have h := (RhTail.physical_fourier_tail_limit hA
    (by linarith : A < A + 1) hv 0 0 0).1
  have hbeta : RhAnchored.beta 0 = (1 / 2 : ℝ) := by
    norm_num [RhAnchored.beta, RhAnchored.archIndex]
  rw [hbeta] at h
  unfold FullArchFiniteEnergy
  rw [h]
  exact ENNReal.ofReal_lt_top

end RhPrimitiveFormDomain
#print axioms RhPrimitiveFormDomain.physical_primitive_full_arch_finite
