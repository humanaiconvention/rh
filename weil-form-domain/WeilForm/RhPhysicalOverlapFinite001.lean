import RhPhysicalProjectionSchur001
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! Exact finite physical overlap algebra on the actual weighted core.
This module proves a limit/invertibility implication; the subsequent native
old-null lift instantiation supplies its actual convergence hypothesis.
-/
set_option maxHeartbeats 0
noncomputable section
open Set Filter
open scoped Topology BigOperators
namespace RhPhysicalOverlapFinite
open RhWeightedMeasureEmbedding RhFlatSmoothCore RhPhysicalProjectionSchur
open RhFixedPhysicalSchurMatrix

def overlap {d : ℕ} {R : ℝ} (p w : Fin d → FlatCoreSpace R) :
    Matrix (Fin d) (Fin d) ℝ := fun i j =>
  inner ℝ (physicalEmbedding (p i : WeightedSpace))
    (physicalEmbedding (w j : WeightedSpace))

lemma overlap_self {d : ℕ} {R : ℝ} (p : Fin d → FlatCoreSpace R)
    (hp : Orthonormal ℝ (fun i => physicalEmbedding (p i : WeightedSpace))) :
    overlap p p = 1 := by
  ext i j
  exact (orthonormal_iff_ite.mp hp) i j

lemma coefficients_combination {d : ℕ} {R : ℝ}
    (p w : Fin d → FlatCoreSpace R) (c : Fin d → ℝ) :
    coefficients p (combination w c) = (overlap p w).mulVec c := by
  funext i
  unfold coefficients
  rw [physical_combination, inner_sum]
  simp only [real_inner_smul_right, Matrix.mulVec, dotProduct, overlap]
  apply Finset.sum_congr rfl
  intro j hj
  ring

lemma combination_mem_span {d : ℕ} {R : ℝ}
    (w : Fin d → FlatCoreSpace R) (c : Fin d → ℝ) :
    combination w c ∈ Submodule.span ℝ (Set.range w) := by
  apply Submodule.sum_mem
  intro i hi
  exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i))

/-- Finite invertibility gives surjectivity of the actual physical
coordinates on the span of the target family, without a projection assumption. -/
theorem surjective_coordinates_of_det_ne_zero {d : ℕ} {R : ℝ}
    (p w : Fin d → FlatCoreSpace R) (hdet : (overlap p w).det ≠ 0) :
    ∀ a : Fin d → ℝ, ∃ F : FlatCoreSpace R,
      F ∈ Submodule.span ℝ (Set.range w) ∧ coefficients p F = a := by
  have hu : IsUnit (overlap p w) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet)
  have hs : Function.Surjective (overlap p w).mulVec :=
    Matrix.mulVec_surjective_iff_isUnit.mpr hu
  intro a
  obtain ⟨c, hc⟩ := hs a
  exact ⟨combination w c, combination_mem_span w c,
    (coefficients_combination p w c).trans hc⟩

/-- Entrywise physical L2 convergence is enough; no unbounded operator or
arithmetic positivity premise enters this finite determinant argument. -/
theorem overlap_tendsto_identity {d : ℕ} {R : ℝ} {X : Type*}
    {l : Filter X} (p : Fin d → FlatCoreSpace R)
    (hp : Orthonormal ℝ (fun i => physicalEmbedding (p i : WeightedSpace)))
    (w : X → Fin d → FlatCoreSpace R)
    (hw : ∀ j, Tendsto (fun x => physicalEmbedding (w x j : WeightedSpace))
      l (𝓝 (physicalEmbedding (p j : WeightedSpace)))) :
    Tendsto (fun x => overlap p (w x)) l (𝓝 1) := by
  rw [← overlap_self p hp]
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_pi_nhds.mpr
  intro j
  have hc : Continuous (fun z : WholeSpace =>
      inner ℝ (physicalEmbedding (p i : WeightedSpace)) z) :=
    continuous_const.inner continuous_id
  exact hc.continuousAt.tendsto.comp (hw j)

theorem determinant_tendsto_one {d : ℕ} {R : ℝ} {X : Type*}
    {l : Filter X} (p : Fin d → FlatCoreSpace R)
    (hp : Orthonormal ℝ (fun i => physicalEmbedding (p i : WeightedSpace)))
    (w : X → Fin d → FlatCoreSpace R)
    (hw : ∀ j, Tendsto (fun x => physicalEmbedding (w x j : WeightedSpace))
      l (𝓝 (physicalEmbedding (p j : WeightedSpace)))) :
    Tendsto (fun x => (overlap p (w x)).det) l (𝓝 (1 : ℝ)) := by
  have hm := overlap_tendsto_identity p hp w hw
  have hc : Continuous (fun A : Matrix (Fin d) (Fin d) ℝ => A.det) :=
    continuous_id.matrix_det
  simpa only [Matrix.det_one, Function.comp_def] using hc.continuousAt.tendsto.comp hm

/-- Eventual determinant nonvanishing and physical-coordinate surjectivity
are consequences of the limit to the actual orthonormal Gram matrix. -/
theorem eventually_invertible_and_surjective {d : ℕ} {R : ℝ} {X : Type*}
    {l : Filter X} (p : Fin d → FlatCoreSpace R)
    (hp : Orthonormal ℝ (fun i => physicalEmbedding (p i : WeightedSpace)))
    (w : X → Fin d → FlatCoreSpace R)
    (hw : ∀ j, Tendsto (fun x => physicalEmbedding (w x j : WeightedSpace))
      l (𝓝 (physicalEmbedding (p j : WeightedSpace)))) :
    ∀ᶠ x in l, (overlap p (w x)).det ≠ 0 ∧
      ∀ a : Fin d → ℝ, ∃ F : FlatCoreSpace R,
        F ∈ Submodule.span ℝ (Set.range (w x)) ∧ coefficients p F = a := by
  have hd := (determinant_tendsto_one p hp w hw).eventually_ne (by norm_num : (1 : ℝ) ≠ 0)
  filter_upwards [hd] with x hx
  exact ⟨hx, surjective_coordinates_of_det_ne_zero p (w x) hx⟩

end RhPhysicalOverlapFinite
#print axioms RhPhysicalOverlapFinite.coefficients_combination
#print axioms RhPhysicalOverlapFinite.surjective_coordinates_of_det_ne_zero
#print axioms RhPhysicalOverlapFinite.overlap_tendsto_identity
#print axioms RhPhysicalOverlapFinite.determinant_tendsto_one
#print axioms RhPhysicalOverlapFinite.eventually_invertible_and_surjective

