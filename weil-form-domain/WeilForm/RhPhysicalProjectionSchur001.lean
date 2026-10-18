import RhFixedPhysicalSchurMatrix001
import Mathlib.Analysis.InnerProductSpace.Orthonormal

/-! The finite projector is PHYSICAL-L2 orthogonal, not graph orthogonal.
An explicitly physical-orthonormal family gives an exact full-core P+Q
decomposition and a literal matrix Schur criterion. Nullspace membership or
spanning is not asserted by any theorem in this module. -/
set_option maxHeartbeats 100000
set_option synthInstance.maxHeartbeats 20000
noncomputable section
open Set MeasureTheory
open scoped Topology BigOperators
namespace RhPhysicalProjectionSchur
open RhWeightedMeasureEmbedding RhFlatSmoothCore RhPhysicalOrthogonalSchur
open RhPulledCompleteForm RhFixedPhysicalPulledSchur RhFixedPhysicalSchurMatrix

def coefficients {d : ℕ} {R : ℝ} (p : Fin d → FlatCoreSpace R)
    (F : FlatCoreSpace R) : Fin d → ℝ := fun i =>
  inner ℝ (physicalEmbedding (p i : WeightedSpace)) (physicalEmbedding (F : WeightedSpace))

def projection {d : ℕ} {R : ℝ} (p : Fin d → FlatCoreSpace R)
    (F : FlatCoreSpace R) : FlatCoreSpace R := combination p (coefficients p F)

lemma physical_combination {d : ℕ} {R : ℝ} (p : Fin d → FlatCoreSpace R)
    (c : Fin d → ℝ) :
    physicalEmbedding (combination p c : WeightedSpace) =
      ∑ i, c i • physicalEmbedding (p i : WeightedSpace) := by
  simp [combination]

lemma coefficients_combination {d : ℕ} {R : ℝ} (p : Fin d → FlatCoreSpace R)
    (hp : Orthonormal ℝ (fun i => physicalEmbedding (p i : WeightedSpace)))
    (c : Fin d → ℝ) : coefficients p (combination p c) = c := by
  funext i
  unfold coefficients
  rw [physical_combination]
  exact hp.inner_right_fintype c i

theorem projection_idempotent {d : ℕ} {R : ℝ} (p : Fin d → FlatCoreSpace R)
    (hp : Orthonormal ℝ (fun i => physicalEmbedding (p i : WeightedSpace)))
    (F : FlatCoreSpace R) : projection p (projection p F) = projection p F := by
  unfold projection
  rw [coefficients_combination p hp]

/-- The actual physical-orthogonal remainder, retained in the SAME core. -/
def remainder {d : ℕ} {R : ℝ} (p : Fin d → FlatCoreSpace R)
    (hp : Orthonormal ℝ (fun i => physicalEmbedding (p i : WeightedSpace)))
    (F : FlatCoreSpace R) : ComplementSpace R p :=
  ⟨(F - projection p F : FlatCoreSpace R), by
    apply (mem_complement_iff R p _).mpr
    refine ⟨(F - projection p F).property, ?_⟩
    intro i
    change inner ℝ (physicalEmbedding (p i : WeightedSpace))
      (physicalEmbedding ((F : WeightedSpace) - (projection p F : WeightedSpace))) = 0
    rw [map_sub, inner_sub_right]
    have hi := congrFun (coefficients_combination p hp (coefficients p F)) i
    change inner ℝ (physicalEmbedding (p i : WeightedSpace))
      (physicalEmbedding (projection p F : WeightedSpace)) = coefficients p F i at hi
    rw [hi]
    simp only [coefficients, sub_self]⟩

theorem physical_decomposition {d : ℕ} {R : ℝ} (p : Fin d → FlatCoreSpace R)
    (hp : Orthonormal ℝ (fun i => physicalEmbedding (p i : WeightedSpace)))
    (F : FlatCoreSpace R) :
    projection p F + toCore R p (remainder p hp F) = F := by
  apply Subtype.ext
  change (projection p F : WeightedSpace) +
    ((F : WeightedSpace) - (projection p F : WeightedSpace)) = (F : WeightedSpace)
  abel

/-- Full actual common-core positivity is EXACTLY the finite matrix Schur
condition under an explicit physical orthonormal-family premise and the
already constructed complement coercivity. This theorem proves no sign. -/
theorem full_core_schur_iff {d : ℕ} {R r : ℝ} (hr : 1 ≤ r)
    (C : ℝ) (N : ℕ) (p : Fin d → FlatCoreSpace R)
    (hp : Orthonormal ℝ (fun i => physicalEmbedding (p i : WeightedSpace)))
    {mu eta : ℝ} (h : Control hr C N p mu eta) :
    (∀ F : FlatCoreSpace R, 0 ≤ pulledForm hr C N F F) ↔
      ∀ c : Fin d → ℝ, 0 ≤ ∑ i, ∑ j, c i * c j * schurMatrix hr C N p h i j := by
  constructor
  · intro hall
    apply (family_schur_iff hr C N p h).mp
    intro c q
    exact hall (combination p c + toCore R p q)
  · intro hall F
    have hfam := (family_schur_iff hr C N p h).mpr hall
    have hv := hfam (coefficients p F) (remainder p hp F)
    change 0 ≤ pulledForm hr C N (projection p F + toCore R p (remainder p hp F))
      (projection p F + toCore R p (remainder p hp F)) at hv
    simpa only [physical_decomposition] using hv

end RhPhysicalProjectionSchur
#print axioms RhPhysicalProjectionSchur.projection_idempotent
#print axioms RhPhysicalProjectionSchur.physical_decomposition
#print axioms RhPhysicalProjectionSchur.full_core_schur_iff