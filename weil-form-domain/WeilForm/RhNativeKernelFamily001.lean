import RhNativeCompactGap001
import RhPhysicalOrthogonalSchur001
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! An actual finite basis of the native nullspace and its derived PHYSICAL
complement gap. Only positivity at the declared finite radius is assumed.
No outward residual sign or all-radius continuation is inferred. -/
set_option maxHeartbeats 0
noncomputable section
open Set MeasureTheory
open scoped Topology BigOperators
namespace RhNativeKernelFamily
open RhWeightedMeasureEmbedding RhNativeCompleteBilinear RhFlatSmoothCore
open RhNativeCompactGap

def dimension (R C : ℝ) (N : ℕ) : ℕ := Module.finrank ℝ (form R C N).ker

def basis {R : ℝ} (hR : 0 < R) (C : ℝ) (N : ℕ)
    (hpos : ∀ x : FlatCoreSpace R,
      0 ≤ completeForm R C N (x : WeightedSpace) (x : WeightedSpace)) :
    Module.Basis (Fin (dimension R C N)) ℝ (form R C N).ker := by
  letI : FiniteDimensional ℝ (form R C N).ker := finite_nullspace hR C N hpos
  letI : Module.Free ℝ (form R C N).ker := Module.Free.of_divisionRing ℝ (form R C N).ker
  exact Module.finBasis ℝ (form R C N).ker

def family {R : ℝ} (hR : 0 < R) (C : ℝ) (N : ℕ)
    (hpos : ∀ x : FlatCoreSpace R,
      0 ≤ completeForm R C N (x : WeightedSpace) (x : WeightedSpace)) :
    Fin (dimension R C N) → FlatCoreSpace R :=
  fun i => (basis hR C N hpos i : FlatCoreSpace R)

lemma family_mem_kernel {R : ℝ} (hR : 0 < R) (C : ℝ) (N : ℕ)
    (hpos : ∀ x : FlatCoreSpace R,
      0 ≤ completeForm R C N (x : WeightedSpace) (x : WeightedSpace))
    (i : Fin (dimension R C N)) : family hR C N hpos i ∈ (form R C N).ker :=
  (basis hR C N hpos i).property

/-- Literal finite coordinate representation of EVERY null vector. -/
theorem kernel_spanning {R : ℝ} (hR : 0 < R) (C : ℝ) (N : ℕ)
    (hpos : ∀ x : FlatCoreSpace R,
      0 ≤ completeForm R C N (x : WeightedSpace) (x : WeightedSpace))
    (z : FlatCoreSpace R) (hz : z ∈ (form R C N).ker) :
    ∃ c : Fin (dimension R C N) → ℝ,
      z = ∑ i, c i • family hR C N hpos i := by
  let z0 : (form R C N).ker := ⟨z,hz⟩
  refine ⟨fun i => (basis hR C N hpos).repr z0 i, ?_⟩
  have h := (basis hR C N hpos).sum_repr z0
  have hh := congrArg (fun x : (form R C N).ker => (x : FlatCoreSpace R)) h
  simpa only [family, Submodule.coe_sum, Submodule.coe_smul_of_tower] using hh.symm

/-- The physical-gap premise of the existing exact Schur machinery is derived
for a basis of the ACTUAL nullspace, rather than an arbitrary chosen family. -/
theorem actual_physical_gap {R : ℝ} (hR : 0 < R) (C : ℝ) (N : ℕ)
    (hpos : ∀ x : FlatCoreSpace R,
      0 ≤ completeForm R C N (x : WeightedSpace) (x : WeightedSpace)) :
    ∃ mu : ℝ, 0 < mu ∧ RhPhysicalOrthogonalSchur.PhysicalGap R C N
      (family hR C N hpos) mu := by
  obtain ⟨mu,hmu,hgap⟩ := physical_complement_gap hR C N hpos
  refine ⟨mu,hmu,?_⟩
  intro q
  have hq := (RhPhysicalOrthogonalSchur.mem_complement_iff R
    (family hR C N hpos) (q : WeightedSpace)).mp q.property
  let x : FlatCoreSpace R := ⟨(q : WeightedSpace),hq.1⟩
  apply hgap x
  intro z hz
  let l : FlatCoreSpace R →L[ℝ] ℝ := (innerSL ℝ (physical R x)).comp (physical R)
  have hl (i : Fin (dimension R C N)) : l (family hR C N hpos i) = 0 := by
    change inner ℝ (physicalEmbedding (q : WeightedSpace))
      (physicalEmbedding (family hR C N hpos i : WeightedSpace)) = 0
    rw [real_inner_comm]
    exact hq.2 i
  obtain ⟨c,hc⟩ := kernel_spanning hR C N hpos z hz
  change l z = 0
  rw [hc, map_sum]
  simp only [map_smul, smul_eq_mul, hl, mul_zero, Finset.sum_const_zero]

end RhNativeKernelFamily
#print axioms RhNativeKernelFamily.family_mem_kernel
#print axioms RhNativeKernelFamily.kernel_spanning
#print axioms RhNativeKernelFamily.actual_physical_gap



