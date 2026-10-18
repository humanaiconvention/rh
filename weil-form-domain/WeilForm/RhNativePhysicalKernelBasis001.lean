import RhNativeKernelFamily001
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! The native kernel basis is normalized in PHYSICAL L2, not the graph norm.
The actual nullspace is finite only under the explicit base positivity premise. -/
set_option maxHeartbeats 0
noncomputable section
open Set MeasureTheory
open scoped Topology BigOperators
namespace RhNativePhysicalKernelBasis
open RhWeightedMeasureEmbedding RhNativeCompleteBilinear RhFlatSmoothCore RhNativeCompactGap

def kernelPhysical (R C : ℝ) (N : ℕ) : (form R C N).ker →ₗ[ℝ] WholeSpace :=
  (physical R).toLinearMap.comp (form R C N).ker.subtype

lemma kernelPhysical_injective (R C : ℝ) (N : ℕ) : Function.Injective (kernelPhysical R C N) := by
  intro x y h
  apply Subtype.ext
  exact physical_injective R h

def physicalKernel (R C : ℝ) (N : ℕ) : Submodule ℝ WholeSpace :=
  (kernelPhysical R C N).range

def kernelToImage (R C : ℝ) (N : ℕ) : (form R C N).ker ≃ₗ[ℝ] physicalKernel R C N :=
  LinearEquiv.ofInjective (kernelPhysical R C N) (kernelPhysical_injective R C N)

def imageDimension (R C : ℝ) (N : ℕ) : ℕ := Module.finrank ℝ (physicalKernel R C N)

def imageBasis {R : ℝ} (hR : 0 < R) (C : ℝ) (N : ℕ)
    (hpos : ∀ x : FlatCoreSpace R,
      0 ≤ completeForm R C N (x : WeightedSpace) (x : WeightedSpace)) :
    OrthonormalBasis (Fin (imageDimension R C N)) ℝ (physicalKernel R C N) := by
  letI : FiniteDimensional ℝ (form R C N).ker := finite_nullspace hR C N hpos
  letI : FiniteDimensional ℝ (physicalKernel R C N) := by
    change FiniteDimensional ℝ (kernelPhysical R C N).range
    exact Module.Finite.range (kernelPhysical R C N)
  exact stdOrthonormalBasis ℝ (physicalKernel R C N)

def liftedBasis {R : ℝ} (hR : 0 < R) (C : ℝ) (N : ℕ)
    (hpos : ∀ x : FlatCoreSpace R,
      0 ≤ completeForm R C N (x : WeightedSpace) (x : WeightedSpace)) :
    Module.Basis (Fin (imageDimension R C N)) ℝ (form R C N).ker :=
  (imageBasis hR C N hpos).toBasis.map (kernelToImage R C N).symm

def family {R : ℝ} (hR : 0 < R) (C : ℝ) (N : ℕ)
    (hpos : ∀ x : FlatCoreSpace R,
      0 ≤ completeForm R C N (x : WeightedSpace) (x : WeightedSpace)) :
    Fin (imageDimension R C N) → FlatCoreSpace R :=
  fun i => (liftedBasis hR C N hpos i : FlatCoreSpace R)

lemma family_mem_kernel {R : ℝ} (hR : 0 < R) (C : ℝ) (N : ℕ)
    (hpos : ∀ x : FlatCoreSpace R,
      0 ≤ completeForm R C N (x : WeightedSpace) (x : WeightedSpace))
    (i : Fin (imageDimension R C N)) : family hR C N hpos i ∈ (form R C N).ker :=
  (liftedBasis hR C N hpos i).property

lemma physical_family_eq_basis {R : ℝ} (hR : 0 < R) (C : ℝ) (N : ℕ)
    (hpos : ∀ x : FlatCoreSpace R,
      0 ≤ completeForm R C N (x : WeightedSpace) (x : WeightedSpace))
    (i : Fin (imageDimension R C N)) :
    physical R (family hR C N hpos i) = (imageBasis hR C N hpos i : WholeSpace) := by
  change kernelPhysical R C N ((kernelToImage R C N).symm (imageBasis hR C N hpos i)) = _
  exact LinearEquiv.ofInjective_symm_apply _ _

/-- The full family is orthonormal in the ACTUAL physical L2 inner product. -/
theorem family_physical_orthonormal {R : ℝ} (hR : 0 < R) (C : ℝ) (N : ℕ)
    (hpos : ∀ x : FlatCoreSpace R,
      0 ≤ completeForm R C N (x : WeightedSpace) (x : WeightedSpace)) :
    Orthonormal ℝ (fun i => physicalEmbedding (family hR C N hpos i : WeightedSpace)) := by
  classical
  change Orthonormal ℝ (fun i => physical R (family hR C N hpos i))
  apply orthonormal_iff_ite.mpr
  intro i j
  rw [physical_family_eq_basis, physical_family_eq_basis]
  exact (orthonormal_iff_ite.mp (imageBasis hR C N hpos).orthonormal) i j

theorem kernel_spanning {R : ℝ} (hR : 0 < R) (C : ℝ) (N : ℕ)
    (hpos : ∀ x : FlatCoreSpace R,
      0 ≤ completeForm R C N (x : WeightedSpace) (x : WeightedSpace))
    (z : FlatCoreSpace R) (hz : z ∈ (form R C N).ker) :
    ∃ c : Fin (imageDimension R C N) → ℝ,
      z = ∑ i, c i • family hR C N hpos i := by
  let z0 : (form R C N).ker := ⟨z,hz⟩
  refine ⟨fun i => (liftedBasis hR C N hpos).repr z0 i, ?_⟩
  have h := (liftedBasis hR C N hpos).sum_repr z0
  have hh := congrArg (fun x : (form R C N).ker => (x : FlatCoreSpace R)) h
  simpa only [family, Submodule.coe_sum, Submodule.coe_smul_of_tower] using hh.symm

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
  have hl (i : Fin (imageDimension R C N)) : l (family hR C N hpos i) = 0 := by
    change inner ℝ (physicalEmbedding (q : WeightedSpace))
      (physicalEmbedding (family hR C N hpos i : WeightedSpace)) = 0
    rw [real_inner_comm]
    exact hq.2 i
  obtain ⟨c,hc⟩ := kernel_spanning hR C N hpos z hz
  change l z = 0
  rw [hc, map_sum]
  simp only [map_smul, smul_eq_mul, hl, mul_zero, Finset.sum_const_zero]

end RhNativePhysicalKernelBasis
#print axioms RhNativePhysicalKernelBasis.family_physical_orthonormal
#print axioms RhNativePhysicalKernelBasis.kernel_spanning
#print axioms RhNativePhysicalKernelBasis.actual_physical_gap


