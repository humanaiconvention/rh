import RhDilationDefs001
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.ContDiff.RCLike

noncomputable section
open Set MeasureTheory Filter
open scoped Topology BigOperators

namespace RhDilationRank
open RhAnchored

lemma continuous_memLp {A : ℝ} {f : ℝ → ℝ} (hf : Continuous f) :
    MemLp f 2 (physicalMeasure A) := by
  obtain ⟨C,hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hf.continuousOn
  apply MemLp.of_bound hf.aestronglyMeasurable C
  exact ae_restrict_of_forall_mem measurableSet_Icc hC

lemma norm_sq_toLp {A : ℝ} {f : ℝ → ℝ} (hf : MemLp f 2 (physicalMeasure A)) :
    ‖hf.toLp f‖ ^ 2 = ∫ t in interval A, (f t) ^ 2 := by
  rw [←real_inner_self_eq_norm_sq,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with t ht
  rw [ht,Real.inner_apply,pow_two]

lemma moment_eq_inner {A : ℝ} {f w : ℝ → ℝ}
    (hf : MemLp f 2 (physicalMeasure A)) (hw : MemLp w 2 (physicalMeasure A)) :
    (∫ t in interval A, f t * w t) = inner ℝ (hf.toLp f) (hw.toLp w) := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp,hw.coeFn_toLp] with t ht hu
  rw [ht,hu,Real.inner_apply]

/-- Exact integral Cauchy--Schwarz, using actual L2 quotient representatives. -/
theorem moment_cauchy_sq {A : ℝ} {f w : ℝ → ℝ}
    (hf : MemLp f 2 (physicalMeasure A)) (hw : MemLp w 2 (physicalMeasure A)) :
    (∫ t in interval A, f t * w t) ^ 2 ≤
      (∫ t in interval A, (f t) ^ 2) * (∫ t in interval A, (w t) ^ 2) := by
  rw [moment_eq_inner hf hw]
  have h := real_inner_mul_inner_self_le (hf.toLp f) (hw.toLp w)
  rw [real_inner_self_eq_norm_sq,real_inner_self_eq_norm_sq,
    norm_sq_toLp hf,norm_sq_toLp hw] at h
  simpa only [pow_two] using h

lemma l1_sq_le {A : ℝ} (hA : 0 < A) {w : ℝ → ℝ}
    (hw : MemLp w 2 (physicalMeasure A)) :
    (∫ t in interval A, |w t|) ^ 2 ≤ 2 * A * (∫ t in interval A, (w t) ^ 2) := by
  have hOne : MemLp (fun _ : ℝ => (1 : ℝ)) 2 (physicalMeasure A) :=
    continuous_memLp continuous_const
  have hh := moment_cauchy_sq hOne hw.norm
  simpa [Real.norm_eq_abs,integral_const,physicalMeasure,interval,
    Real.volume_Icc,Real.toNNReal_of_nonneg (by linarith : 0 ≤ A - -A),
    abs_sq,max_eq_left (by linarith : 0 ≤ A + A),two_mul] using hh

end RhDilationRank
#print axioms RhDilationRank.continuous_memLp
#print axioms RhDilationRank.moment_cauchy_sq
#print axioms RhDilationRank.l1_sq_le

