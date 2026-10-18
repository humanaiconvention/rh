import RhFlatSmoothCore001
import RhNativeGraphCoercivity001
import RhSchurCovariance001

/-! Concrete PHYSICAL-L2 orthogonal complement of an arbitrary finite family
in the actual closed real smooth core, and its genuinely constructed weak
Schur inverse. Nullness and spanning of an actual kernel are NOT asserted.
The physical positive gap remains explicit; the inverse is not a premise. -/
set_option maxHeartbeats 0
noncomputable section
open Set MeasureTheory
open scoped Topology BigOperators
namespace RhPhysicalOrthogonalSchur
open RhWeightedMeasureEmbedding RhNativeCompleteBilinear RhFlatSmoothCore

/-- Orthogonality is physical L2 orthogonality, not weighted graph orthogonality. -/
def physicalFunctional (p : WeightedSpace) : WeightedSpace →L[ℝ] ℝ :=
  (innerSL ℝ (physicalEmbedding p)).comp physicalEmbedding

lemma physicalFunctional_apply (p q : WeightedSpace) :
    physicalFunctional p q = inner ℝ (physicalEmbedding p) (physicalEmbedding q) := rfl

/-- A single actual submodule of WeightedSpace, retaining the full real core
constraint and every physical orthogonality equation. -/
def complement {d : ℕ} (R : ℝ) (p : Fin d → FlatCoreSpace R) :
    Submodule ℝ WeightedSpace :=
  flatCore R ⊓ ⨅ i, (physicalFunctional (p i : WeightedSpace)).ker

lemma mem_complement_iff {d : ℕ} (R : ℝ) (p : Fin d → FlatCoreSpace R)
    (q : WeightedSpace) :
    q ∈ complement R p ↔ q ∈ flatCore R ∧
      ∀ i, inner ℝ (physicalEmbedding (p i : WeightedSpace)) (physicalEmbedding q) = 0 := by
  simp only [complement, Submodule.mem_inf, Submodule.mem_iInf]
  rfl

theorem complement_isClosed {d : ℕ} (R : ℝ) (p : Fin d → FlatCoreSpace R) :
    IsClosed (complement R p : Set WeightedSpace) := by
  simp only [complement, Submodule.coe_inf, Submodule.coe_iInf]
  exact (flatCore_isClosed R).inter
    (isClosed_iInter (fun i => (physicalFunctional (p i : WeightedSpace)).isClosed_ker))

abbrev ComplementSpace {d : ℕ} (R : ℝ) (p : Fin d → FlatCoreSpace R) := ↥(complement R p)

instance complement_complete {d : ℕ} (R : ℝ) (p : Fin d → FlatCoreSpace R) :
    CompleteSpace (ComplementSpace R p) :=
  (complement_isClosed R p).completeSpace_coe

def form {d : ℕ} (R C : ℝ) (N : ℕ) (p : Fin d → FlatCoreSpace R) :
    ComplementSpace R p →L[ℝ] ComplementSpace R p →L[ℝ] ℝ :=
  RhNativeGraphCoercivity.restrictedForm R C N (complement R p)

lemma form_apply {d : ℕ} (R C : ℝ) (N : ℕ) (p : Fin d → FlatCoreSpace R)
    (x y : ComplementSpace R p) :
    form R C N p x y = completeForm R C N (x : WeightedSpace) (y : WeightedSpace) := rfl

theorem form_symmetric {d : ℕ} (R C : ℝ) (N : ℕ) (p : Fin d → FlatCoreSpace R)
    (x y : ComplementSpace R p) :
    form R C N p x y = form R C N p y x :=
  completeForm_symmetric R C N _ _

/-- The honest still-unproved arithmetic input: a positive PHYSICAL gap on
this actual physical-orthogonal complement. -/
def PhysicalGap {d : ℕ} (R C : ℝ) (N : ℕ) (p : Fin d → FlatCoreSpace R) (mu : ℝ) : Prop :=
  ∀ q : ComplementSpace R p,
    mu * ‖physicalEmbedding (q : WeightedSpace)‖ ^ 2 ≤
      completeForm R C N (q : WeightedSpace) (q : WeightedSpace)

theorem form_isCoercive {d : ℕ} (R C : ℝ) (N : ℕ) (p : Fin d → FlatCoreSpace R)
    {mu : ℝ} (hmu : 0 < mu) (hgap : PhysicalGap R C N p mu) :
    IsCoercive (form R C N p) :=
  RhNativeGraphCoercivity.restricted_isCoercive_of_physical_gap
    R C N (complement R p) hmu hgap

/-- Actual form-space Riesz inverse constructed by Lax-Milgram. It is not
silently identified with an unbounded physical-L2 operator inverse. -/
def inverse {d : ℕ} (R C : ℝ) (N : ℕ) (p : Fin d → FlatCoreSpace R)
    {mu : ℝ} (hmu : 0 < mu) (hgap : PhysicalGap R C N p mu) :
    ComplementSpace R p →L[ℝ] ComplementSpace R p :=
  RhCoerciveSchurInverse.inverse (form R C N p) (form_isCoercive R C N p hmu hgap)

theorem inverse_weak_equation {d : ℕ} (R C : ℝ) (N : ℕ)
    (p : Fin d → FlatCoreSpace R) {mu : ℝ} (hmu : 0 < mu)
    (hgap : PhysicalGap R C N p mu) (b q : ComplementSpace R p) :
    completeForm R C N (inverse R C N p hmu hgap b : WeightedSpace) (q : WeightedSpace) =
      inner ℝ b q :=
  RhCoerciveSchurInverse.inverse_weak_equation
    (form R C N p) (form_isCoercive R C N p hmu hgap) b q

/-- Riesz representative of the COMPLETE actual cross functional, with all
native scalar, rank and prime-power companions still inside completeForm. -/
def crossSource {d : ℕ} (R C : ℝ) (N : ℕ) (p : Fin d → FlatCoreSpace R)
    (v : WeightedSpace) : ComplementSpace R p :=
  (InnerProductSpace.toDual ℝ (ComplementSpace R p)).symm
    ((completeForm R C N v).comp (complement R p).subtypeL)

theorem crossSource_weak {d : ℕ} (R C : ℝ) (N : ℕ)
    (p : Fin d → FlatCoreSpace R) (v : WeightedSpace) (q : ComplementSpace R p) :
    inner ℝ (crossSource R C N p v) q =
      completeForm R C N v (q : WeightedSpace) :=
  InnerProductSpace.toDual_symm_apply

theorem crossSource_full_expansion {d : ℕ} (R C : ℝ) (N : ℕ)
    (p : Fin d → FlatCoreSpace R) (v : WeightedSpace) (q : ComplementSpace R p) :
    inner ℝ (crossSource R C N p v) q =
      archPair v (q : WeightedSpace) -
      C * spatialPair v (q : WeightedSpace) +
      2 * coshPair R v (q : WeightedSpace) -
      2 * sinhPair R v (q : WeightedSpace) -
      ∑ n ∈ Finset.Icc 2 N, RhAllPrime.weight n *
        shiftPair (Real.log (n : ℝ)) v (q : WeightedSpace) := by
  rw [crossSource_weak]
  change archPair v (q : WeightedSpace) +
    boundedPart R C N v (q : WeightedSpace) = _
  rw [boundedPart_apply]
  ring

def residual {d : ℕ} (R C : ℝ) (N : ℕ) (p : Fin d → FlatCoreSpace R)
    {mu : ℝ} (hmu : 0 < mu) (hgap : PhysicalGap R C N p mu) (v : WeightedSpace) : ℝ :=
  completeForm R C N v v -
    inner ℝ (crossSource R C N p v)
      (inverse R C N p hmu hgap (crossSource R C N p v))

lemma whole_form_expansion {d : ℕ} (R C : ℝ) (N : ℕ)
    (p : Fin d → FlatCoreSpace R) (v : WeightedSpace) (q : ComplementSpace R p) :
    completeForm R C N (v + (q : WeightedSpace)) (v + (q : WeightedSpace)) =
      completeForm R C N v v + 2 * inner ℝ (crossSource R C N p v) q +
        form R C N p q q := by
  simp only [map_add, ContinuousLinearMap.add_apply]
  rw [completeForm_symmetric R C N (q : WeightedSpace) v, crossSource_weak]
  rw [form_apply]
  ring

/-- Exact actual arithmetic Schur residual criterion along v+Q. No sign of the
residual is supplied, and Q is not mislabeled as a graph-orthogonal complement. -/
theorem actual_schur_iff {d : ℕ} (R C : ℝ) (N : ℕ)
    (p : Fin d → FlatCoreSpace R) {mu : ℝ} (hmu : 0 < mu)
    (hgap : PhysicalGap R C N p mu) (v : WeightedSpace) :
    (∀ q : ComplementSpace R p,
      0 ≤ completeForm R C N (v + (q : WeightedSpace)) (v + (q : WeightedSpace))) ↔
      0 ≤ residual R C N p hmu hgap v := by
  simp only [whole_form_expansion]
  exact RhCoerciveSchurInverse.nonnegative_iff_residual
    (form R C N p) (form_isCoercive R C N p hmu hgap)
    (form_symmetric R C N p) (completeForm R C N v v) (crossSource R C N p v)

theorem cross_payment_nonnegative {d : ℕ} (R C : ℝ) (N : ℕ)
    (p : Fin d → FlatCoreSpace R) {mu : ℝ} (hmu : 0 < mu)
    (hgap : PhysicalGap R C N p mu) (v : WeightedSpace) :
    0 ≤ inner ℝ (crossSource R C N p v)
      (inverse R C N p hmu hgap (crossSource R C N p v)) :=
  RhCoerciveSchurInverse.cross_payment_nonnegative
    (form R C N p) (form_isCoercive R C N p hmu hgap) _

end RhPhysicalOrthogonalSchur
#print axioms RhPhysicalOrthogonalSchur.mem_complement_iff
#print axioms RhPhysicalOrthogonalSchur.complement_isClosed
#print axioms RhPhysicalOrthogonalSchur.form_isCoercive
#print axioms RhPhysicalOrthogonalSchur.inverse_weak_equation
#print axioms RhPhysicalOrthogonalSchur.crossSource_full_expansion
#print axioms RhPhysicalOrthogonalSchur.actual_schur_iff
#print axioms RhPhysicalOrthogonalSchur.cross_payment_nonnegative
