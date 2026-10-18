import RhCompactPhysicalGap001
import RhCompactPositiveKernel001
import RhFlatSmoothCore001

/-! Native instantiation: the actual closed real complete domain has a finite
nullspace and a PHYSICAL complement gap IF its complete arithmetic form is
nonnegative. No all-radius positivity or residual sign is supplied here. -/
set_option maxHeartbeats 0
noncomputable section
open Set MeasureTheory
open scoped Topology
namespace RhNativeCompactGap
open RhWeightedMeasureEmbedding RhNativeCompleteBilinear RhFlatSmoothCore

def toSupported (R : ℝ) : FlatCoreSpace R →L[ℝ] SupportedSpace R :=
  (Submodule.inclusion (flatCore_supported R)).mkContinuous 1 (fun x => by
    change ‖(x : WeightedSpace)‖ ≤ 1*‖(x : WeightedSpace)‖
    rw [one_mul])

def physical (R : ℝ) : FlatCoreSpace R →L[ℝ] WholeSpace :=
  physicalEmbedding.comp (flatCore R).subtypeL

def form (R C : ℝ) (N : ℕ) : FlatCoreSpace R →L[ℝ] FlatCoreSpace R →L[ℝ] ℝ :=
  RhNativeGraphCoercivity.restrictedForm R C N (flatCore R)

lemma physical_injective (R : ℝ) : Function.Injective (physical R) := by
  intro x y h
  apply Subtype.ext
  exact physicalEmbedding_injective h

/-- Actual compactness, on the genuine real domain, is inherited from the
proved whole-complex supported complete-domain embedding. -/
theorem physical_compact {R : ℝ} (hR : 0 < R) : IsCompactOperator (physical R) := by
  exact (RhSupportedCompactEmbedding.physical_embedding_compact hR).comp_clm (toSupported R)

lemma form_symmetric (R C : ℝ) (N : ℕ) (x y : FlatCoreSpace R) :
    form R C N x y = form R C N y x :=
  completeForm_symmetric R C N x y

lemma actual_graph_control (R C : ℝ) (N : ℕ) (x : FlatCoreSpace R) :
    ‖x‖^2 ≤ form R C N x x +
      (RhCompleteFormBound.boundConstant R C N+1)*‖physical R x‖^2 :=
  RhNativeGraphCoercivity.native_graph_control R C N x

/-- Finite nullspace is a consequence of the ACTUAL analytic compactness and
native graph control, conditional only on nonnegativity at this radius. -/
theorem finite_nullspace {R : ℝ} (hR : 0 < R) (C : ℝ) (N : ℕ)
    (hpos : ∀ x : FlatCoreSpace R,
      0 ≤ completeForm R C N (x : WeightedSpace) (x : WeightedSpace)) :
    FiniteDimensional ℝ (form R C N).ker := by
  apply RhCompactPositiveKernel.finite_nullspace (form R C N) (physical R)
    (physical_compact hR) (by
      have h := RhCompleteFormBound.boundConstant_nonneg R C N
      positivity) hpos (form_symmetric R C N) (actual_graph_control R C N)

/-- No physical gap is assumed: it is derived on the PHYSICAL orthogonal
complement of the entire actual nullspace. -/
theorem physical_complement_gap {R : ℝ} (hR : 0 < R) (C : ℝ) (N : ℕ)
    (hpos : ∀ x : FlatCoreSpace R,
      0 ≤ completeForm R C N (x : WeightedSpace) (x : WeightedSpace)) :
    ∃ mu : ℝ, 0 < mu ∧ ∀ x : FlatCoreSpace R,
      (∀ z : FlatCoreSpace R, z ∈ (form R C N).ker →
        inner ℝ (physical R x) (physical R z) = 0) →
      mu*‖physical R x‖^2 ≤ completeForm R C N (x : WeightedSpace) (x : WeightedSpace) := by
  obtain ⟨mu,hmu,hgap⟩ := RhCompactPhysicalGap.physical_gap (form R C N) (physical R)
    (physical_compact hR) (by
      have h := RhCompleteFormBound.boundConstant_nonneg R C N
      positivity) hpos (actual_graph_control R C N)
  refine ⟨mu,hmu,?_⟩
  intro x hx
  apply hgap x
  intro z hz
  exact hx z (RhCompactPositiveSequence.zero_diagonal_radical (form R C N)
    (form_symmetric R C N) hpos hz)

end RhNativeCompactGap
#print axioms RhNativeCompactGap.physical_compact
#print axioms RhNativeCompactGap.finite_nullspace
#print axioms RhNativeCompactGap.physical_complement_gap
