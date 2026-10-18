import RhCompletePrimitiveDictionary001
import RhDilationRankL2001
import RhDilationShift001
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
The actual complete bounded part at any finite radius is controlled in the
primitive L2 mass. Both ranks and every exact prime-power weight remain in the
form itself. The resulting shifted quadratic bounds assert semiboundedness,
not positivity of the unshifted arithmetic form or a constructed closed normed
space. All actual Fourier energies in the physical theorem are finite by the
accepted all-radius primitive-energy theorem.
-/
noncomputable section
open Set MeasureTheory
open scoped Topology BigOperators ENNReal
namespace RhCompleteFormBound
open RhAnchored RhAllPrime RhCompletePrimitiveDictionary

/-- Primitive mass, with the actual restricted Lebesgue measure. -/
def mass (R : ℝ) (w : ℝ → ℝ) : ℝ := ∫ t in interval R, (w t) ^ 2

/-- The complete native scalar, BOTH ranks, and exact finite prime-power sum. -/
def boundedPart (R C : ℝ) (N : ℕ) (w : ℝ → ℝ) : ℝ :=
  rankScalar R C w -
    ∑ n ∈ Finset.Icc 2 N, weight n *
      (∫ t in interval R, primeShift R (Real.log (n : ℝ)) w t * w t)

/-- No simplification or truncation of the profile masses is required. -/
def rankCost (R C : ℝ) : ℝ :=
  |C| + 2 * (∫ t in interval R, (Real.cosh (t / 2)) ^ 2) +
    2 * (∫ t in interval R, (Real.sinh (t / 2)) ^ 2)

/-- Auxiliary norm constant; the coefficients inside the form retain their signs. -/
def boundConstant (R C : ℝ) (N : ℕ) : ℝ :=
  rankCost R C + 2 * ∑ n ∈ Finset.Icc 2 N, |weight n|

lemma mass_nonneg (R : ℝ) (w : ℝ → ℝ) : 0 ≤ mass R w :=
  integral_nonneg (fun _ => sq_nonneg _)

lemma rankCost_nonneg (R C : ℝ) : 0 ≤ rankCost R C := by
  unfold rankCost
  positivity

lemma boundConstant_nonneg (R C : ℝ) (N : ℕ) : 0 ≤ boundConstant R C N := by
  unfold boundConstant
  exact add_nonneg (rankCost_nonneg R C)
    (mul_nonneg (by norm_num) (Finset.sum_nonneg (fun _ _ => abs_nonneg _)))

/-- Finite weighted two-shift bookkeeping, with no infinite sum exchange. -/
theorem finite_weighted_abs_bound {ι : Type*} (s : Finset ι) (b c : ι → ℝ)
    (M : ℝ) (hc : ∀ i ∈ s, |c i| ≤ 2 * M) :
    |∑ i ∈ s, b i * c i| ≤ 2 * (∑ i ∈ s, |b i|) * M := by
  calc
    |∑ i ∈ s, b i * c i| ≤ ∑ i ∈ s, |b i * c i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i ∈ s, |b i| * |c i| := by simp only [abs_mul]
    _ ≤ ∑ i ∈ s, |b i| * (2 * M) := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left (hc i hi) (abs_nonneg _)
    _ = 2 * (∑ i ∈ s, |b i|) * M := by
      rw [← Finset.sum_mul]
      ring

/-- Both actual moment squares are bounded using their L2 quotient semantics. -/
theorem rankScalar_abs_bound {R : ℝ} {w : ℝ → ℝ}
    (hw : MemLp w 2 (physicalMeasure R)) (C : ℝ) :
    |rankScalar R C w| ≤ rankCost R C * mass R w := by
  have hc := RhDilationRank.moment_cauchy_sq
    (RhDilationRank.continuous_memLp (f := fun t : ℝ => Real.cosh (t / 2))
      (by fun_prop)) hw
  have hs := RhDilationRank.moment_cauchy_sq
    (RhDilationRank.continuous_memLp (f := fun t : ℝ => Real.sinh (t / 2))
      (by fun_prop)) hw
  have hN := mass_nonneg R w
  have hcm : 0 ≤ ∫ t in interval R, (Real.cosh (t / 2)) ^ 2 :=
    integral_nonneg (fun _ => sq_nonneg _)
  have hsm : 0 ≤ ∫ t in interval R, (Real.sinh (t / 2)) ^ 2 :=
    integral_nonneg (fun _ => sq_nonneg _)
  have hCp := mul_le_mul_of_nonneg_right (le_abs_self C) hN
  have hCm := mul_le_mul_of_nonneg_right (neg_abs_le C) hN
  have hCM := mul_nonneg hcm hN
  have hSM := mul_nonneg hsm hN
  apply abs_le.mpr
  unfold rankScalar rankCost
  unfold mass at hN hCp hCm hCM hSM ⊢
  constructor <;> nlinarith [sq_nonneg (∫ t in interval R, Real.cosh (t / 2) * w t),
    sq_nonneg (∫ t in interval R, Real.sinh (t / 2) * w t)]

/-- The sum is the actual arithmetic sum, with both zero-extended delays. -/
theorem arithmetic_abs_bound {R : ℝ} {w : ℝ → ℝ}
    (hw : MemLp w 2 (physicalMeasure R)) (N : ℕ) :
    |∑ n ∈ Finset.Icc 2 N, weight n *
      (∫ t in interval R, primeShift R (Real.log (n : ℝ)) w t * w t)| ≤
        2 * (∑ n ∈ Finset.Icc 2 N, |weight n|) * mass R w := by
  apply finite_weighted_abs_bound
  intro n hn
  exact RhDilation.actual_shift_abs_bound hw (Real.log (n : ℝ))

/-- Absolute control of the entire bounded part at arbitrary radius and cutoff. -/
theorem complete_boundedPart_abs_bound {R : ℝ} {w : ℝ → ℝ}
    (hw : MemLp w 2 (physicalMeasure R)) (C : ℝ) (N : ℕ) :
    |boundedPart R C N w| ≤ boundConstant R C N * mass R w := by
  unfold boundedPart
  calc
    |rankScalar R C w -
        ∑ n ∈ Finset.Icc 2 N, weight n *
          (∫ t in interval R, primeShift R (Real.log (n : ℝ)) w t * w t)| ≤
        |rankScalar R C w| +
          |∑ n ∈ Finset.Icc 2 N, weight n *
            (∫ t in interval R, primeShift R (Real.log (n : ℝ)) w t * w t)| :=
      by
        simpa only [sub_zero, zero_sub, abs_neg] using
          (abs_sub_le (rankScalar R C w) 0
            (∑ n ∈ Finset.Icc 2 N, weight n *
              (∫ t in interval R, primeShift R (Real.log (n : ℝ)) w t * w t)))
    _ ≤ rankCost R C * mass R w +
        2 * (∑ n ∈ Finset.Icc 2 N, |weight n|) * mass R w :=
      add_le_add (rankScalar_abs_bound hw C) (arithmetic_abs_bound hw N)
    _ = boundConstant R C N * mass R w := by unfold boundConstant; ring

/-- Actual finite positive archimedean value on the physical anchored primitive. -/
def actualArch (R : ℝ) (v : ℝ → ℝ)
    (hv : MemLp v 2 (physicalMeasure R)) : ℝ :=
  (RhTail.fullFrequencyEnergy (1 / 2)
    (RhTail.physicalFourierVector R (primitive R v) (primitive_memLp hv))).toReal

/-- Repackage the accepted complete physical identity without changing a weight. -/
theorem actual_complete_decomposition {R : ℝ} (hR : 0 < R)
    {v : ℝ → ℝ} (hv : MemLp v 2 (physicalMeasure R)) (N : ℕ) :
    kernelQuadratic R (completeKernel N) v =
      actualArch R v hv + boundedPart R archConstant N (primitive R v) := by
  rw [complete_cutoff_native_identity hR hv N]
  unfold actualArch boundedPart
  ring

/-- Positive shifted complete quadratic value is equivalent to the graph value.
This proves neither positivity of the original form nor closure of its domain. -/
theorem actual_shifted_complete_bounds {R : ℝ} (hR : 0 < R)
    {v : ℝ → ℝ} (hv : MemLp v 2 (physicalMeasure R)) (N : ℕ) :
    actualArch R v hv + mass R (primitive R v) ≤
      kernelQuadratic R (completeKernel N) v +
        (boundConstant R archConstant N + 1) * mass R (primitive R v) ∧
    kernelQuadratic R (completeKernel N) v +
        (boundConstant R archConstant N + 1) * mass R (primitive R v) ≤
      actualArch R v hv +
        (2 * boundConstant R archConstant N + 1) * mass R (primitive R v) := by
  have hb := complete_boundedPart_abs_bound (primitive_memLp hv) archConstant N
  have hlo := (abs_le.mp hb).1
  have hup := (abs_le.mp hb).2
  rw [actual_complete_decomposition hR hv N]
  constructor <;> nlinarith

/-- The same two-sided comparison for the native floor(exp(2R)) radius kernel. -/
theorem all_radius_shifted_complete_bounds {R : ℝ} (hR : 0 < R)
    {v : ℝ → ℝ} (hv : MemLp v 2 (physicalMeasure R)) :
    actualArch R v hv + mass R (primitive R v) ≤
      kernelQuadratic R (radiusKernel R) v +
        (boundConstant R archConstant (radiusCutoff R) + 1) * mass R (primitive R v) ∧
    kernelQuadratic R (radiusKernel R) v +
        (boundConstant R archConstant (radiusCutoff R) + 1) * mass R (primitive R v) ≤
      actualArch R v hv +
        (2 * boundConstant R archConstant (radiusCutoff R) + 1) * mass R (primitive R v) :=
  actual_shifted_complete_bounds hR hv (radiusCutoff R)

end RhCompleteFormBound
#print axioms RhCompleteFormBound.finite_weighted_abs_bound
#print axioms RhCompleteFormBound.rankScalar_abs_bound
#print axioms RhCompleteFormBound.arithmetic_abs_bound
#print axioms RhCompleteFormBound.complete_boundedPart_abs_bound
#print axioms RhCompleteFormBound.actual_complete_decomposition
#print axioms RhCompleteFormBound.actual_shifted_complete_bounds
#print axioms RhCompleteFormBound.all_radius_shifted_complete_bounds
