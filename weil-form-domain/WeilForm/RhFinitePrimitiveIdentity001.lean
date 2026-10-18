import RhAnchoredFluxIdentity001
import RhAnchoredFormula001

/-!
Unconditional finite-cutoff primitive transfer for the actual anchored kernel.
The only analytic hypothesis on v is membership in L2 on [-A,A].
The shift geometry is the first-window regime 0 < A < L.
No positivity, omitted-tail estimate, or numerical matrix enclosure is asserted.
-/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology Interval BigOperators
namespace RhAnchored

theorem finite_J_Schur_identity {A L : ℝ} (hA : 0 < A) (hAL : A < L)
    {v : ℝ → ℝ} (hv : MemLp v 2 (physicalMeasure A))
    (C α : ℝ) (J : ℕ) :
    (∫ t in interval A, ∫ u in interval A,
      finiteKernel C α L J t u * v u * v t) =
    ∫ t in interval A,
      nativeOperator A C α L J (primitive A v) t * primitive A v t := by
  have he : firstFlux A C α L J (primitive A v) =
      nativeFlux A C α L J (primitive A v) := by
    funext t
    exact firstFlux_eq_nativeFlux hA hAL hv C α J t
  apply finite_J_identity_of_flux_derivative hA hv C α L J
  · rw [he]
    exact nativeFlux_ac hA hAL hv C α J
  · rw [he]
    exact nativeFlux_ae_deriv hA hAL hv C α J

theorem finite_J_Schur_identity_Lp {A L : ℝ} (hA : 0 < A) (hAL : A < L)
    (v : PhysicalSpace A) (C α : ℝ) (J : ℕ) :
    (∫ t in interval A, ∫ u in interval A,
      finiteKernel C α L J t u * v u * v t) =
    ∫ t in interval A,
      nativeOperator A C α L J (primitive A v) t * primitive A v t :=
  finite_J_Schur_identity hA hAL (Lp.memLp v) C α J

end RhAnchored
#print axioms RhAnchored.finite_J_Schur_identity
#print axioms RhAnchored.finite_J_Schur_identity_Lp
