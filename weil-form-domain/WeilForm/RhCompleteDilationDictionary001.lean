import RhCompleteFormBound001
import RhDilationRankPhysical001
import RhDilationShift001
import RhAllPrimeCutoff001

/-! Exact all-radius transported complete form in physical primitive coordinates.
Unlike the historical two-prime transport, this theorem has no R<log(2)
restriction. A single exact finite arithmetic horizon can be retained.
The positive archimedean term is left as its actual finite energy, not estimated.
-/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology BigOperators
namespace RhCompleteDilationDictionary
open RhAnchored RhAllPrime RhCompletePrimitiveDictionary RhCompleteFormBound
open RhDilation RhDilationRank

lemma rankScalar_as_rankForm (R C : ℝ) (w : ℝ → ℝ) :
    rankScalar R C w = -C * mass R w + rankForm R 1 w := by
  simp only [rankScalar, mass, rankForm, moment, coshProfile, sinhProfile,
    profile, Real.sqrt_one, one_mul]
  ring

/-- Every scalar, rank profile and exact prime-power delay is transported.
No cutoff differentiation and no single-prime substitution occurs. -/
theorem complete_cutoff_dilation_dictionary {r A : ℝ} (hr : 0 < r) (hA : 0 < A)
    {v : ℝ → ℝ} (hv : MemLp v 2 (physicalMeasure (r * A))) (N : ℕ) :
    kernelQuadratic (r * A) (completeKernel N) v =
      actualArch (r * A) v hv - archConstant * mass A (primitive A (pullback r v)) +
        rankForm A r (primitive A (pullback r v)) -
        (∑ n ∈ Finset.Icc 2 N, weight n *
          (∫ t in interval A,
            primeShift A (Real.log (n : ℝ) / r) (primitive A (pullback r v)) t *
              primitive A (pullback r v) t)) := by
  let w := primitive A (pullback r v)
  have hw : MemLp w 2 (physicalMeasure A) := primitive_memLp (pullback_memLp hr hv)
  have hd : primitive (r * A) v = dilate r w := by
    funext t
    exact (dilate_primitive_pullback hr A v t).symm
  have hmass : mass (r * A) (dilate r w) = mass A w :=
    physical_square_isometry hr hw
  rw [actual_complete_decomposition (mul_pos hr hA) hv N]
  unfold boundedPart
  rw [rankScalar_as_rankForm, hd, hmass, physical_rank_dilate hA hr]
  simp_rw [shift_dilation hr]
  dsimp only [w]
  ring

/-- Equality with any sufficiently large single exact horizon on this support. -/
theorem radius_quadratic_fixed_horizon {R : ℝ} (hR : 0 ≤ R) (N : ℕ)
    (hN : radiusCutoff R ≤ N) (v : ℝ → ℝ) :
    kernelQuadratic R (radiusKernel R) v = kernelQuadratic R (completeKernel N) v := by
  unfold kernelQuadratic
  apply setIntegral_congr_fun measurableSet_Icc
  intro t ht
  apply setIntegral_congr_fun measurableSet_Icc
  intro u hu
  change radiusKernel R t u * v u * v t = completeKernel N t u * v u * v t
  rw [radius_cutoff_stability hR N hN ht hu]

/-- Native radius kernel, all real positive r and A, with a declared common
horizon N. Inactive hinges are zero exactly, including threshold null sets. -/
theorem all_radius_fixed_horizon_dilation {r A : ℝ} (hr : 0 < r) (hA : 0 < A)
    {v : ℝ → ℝ} (hv : MemLp v 2 (physicalMeasure (r * A))) (N : ℕ)
    (hN : radiusCutoff (r * A) ≤ N) :
    kernelQuadratic (r * A) (radiusKernel (r * A)) v =
      actualArch (r * A) v hv - archConstant * mass A (primitive A (pullback r v)) +
        rankForm A r (primitive A (pullback r v)) -
        (∑ n ∈ Finset.Icc 2 N, weight n *
          (∫ t in interval A,
            primeShift A (Real.log (n : ℝ) / r) (primitive A (pullback r v)) t *
              primitive A (pullback r v) t)) := by
  rw [radius_quadratic_fixed_horizon (mul_pos hr hA).le N hN]
  exact complete_cutoff_dilation_dictionary hr hA hv N

end RhCompleteDilationDictionary
#print axioms RhCompleteDilationDictionary.complete_cutoff_dilation_dictionary
#print axioms RhCompleteDilationDictionary.radius_quadratic_fixed_horizon
#print axioms RhCompleteDilationDictionary.all_radius_fixed_horizon_dilation
