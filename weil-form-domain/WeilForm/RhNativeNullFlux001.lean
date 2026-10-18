import RhLiteralSupportForm001
import RhZeroDiagonalPairing001
import RhNativeGraphCoercivity001

/-! Actual native support-inclusion null flux criterion. All rank and
prime-power companions are retained in ONE complete cross term. This module
neither proves an actual null vector nor determines its total exterior flux. -/
noncomputable section
namespace RhNativeNullFlux
open RhWeightedMeasureEmbedding RhFlatSmoothCore RhNativeCompleteBilinear
open RhLiteralSupportForm

/-- An old null vector is a legitimate complete-domain vector in the larger
window, without any spatial dilation or graph-projection substitution. -/
def includeCore {R S : ℝ} (hRS : R ≤ S) (p : FlatCoreSpace R) : FlatCoreSpace S :=
  ⟨(p : WeightedSpace), flatCore_mono hRS p.property⟩

/-- Positivity in the larger window forces EXACT TOTAL flux annihilation.
No individual prime/rank component is declared to vanish. -/
theorem outward_positive_requires_total_flux_zero {R S : ℝ} (hRS : R ≤ S)
    (C : ℝ) (N : ℕ) (p : FlatCoreSpace R)
    (hp : completeForm R C N (p : WeightedSpace) (p : WeightedSpace) = 0)
    (hpos : ∀ x : FlatCoreSpace S,
      0 ≤ completeForm S C N (x : WeightedSpace) (x : WeightedSpace)) :
    ∀ g : FlatCoreSpace S, completeForm S C N (p : WeightedSpace) (g : WeightedSpace) = 0 := by
  let B := RhNativeGraphCoercivity.restrictedForm S C N (flatCore S)
  have hs : ∀ x y : FlatCoreSpace S, B x y = B y x :=
    fun x y => completeForm_symmetric S C N _ _
  have hpS : B (includeCore hRS p) (includeCore hRS p) = 0 :=
    old_null_diagonal_stays_zero hRS C N p hp
  exact RhZeroDiagonalPairing.positive_zero_forces_cross_zero B hs hpos (includeCore hRS p) hpS

/-- If the COMPLETE native flux is nonzero, the literal larger-window form
has an exact negative vector. This is conditional, not an observed failure. -/
theorem nonzero_total_flux_negative_witness {R S : ℝ} (hRS : R ≤ S)
    (C : ℝ) (N : ℕ) (p : FlatCoreSpace R) (g : FlatCoreSpace S)
    (hp : completeForm R C N (p : WeightedSpace) (p : WeightedSpace) = 0)
    (hb : completeForm S C N (p : WeightedSpace) (g : WeightedSpace) ≠ 0) :
    ∃ x : FlatCoreSpace S, completeForm S C N (x : WeightedSpace) (x : WeightedSpace) = -1 := by
  let B := RhNativeGraphCoercivity.restrictedForm S C N (flatCore S)
  have hs : ∀ x y : FlatCoreSpace S, B x y = B y x :=
    fun x y => completeForm_symmetric S C N _ _
  have hpS : B (includeCore hRS p) (includeCore hRS p) = 0 :=
    old_null_diagonal_stays_zero hRS C N p hp
  refine ⟨(-(B g g + 1) / (2 * B (includeCore hRS p) g)) • includeCore hRS p + g, ?_⟩
  exact RhZeroDiagonalPairing.negative_witness_exact B hs (includeCore hRS p) g hpS hb

end RhNativeNullFlux
#print axioms RhNativeNullFlux.outward_positive_requires_total_flux_zero
#print axioms RhNativeNullFlux.nonzero_total_flux_negative_witness
