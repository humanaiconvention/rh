import JensenWeights
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! UNCOMPILED bounded preparation: pointwise scalar Jensen kernel only.
No compiler, admission, axiom output, measure theorem or acceptance exists. -/


/-!
# Jensen factorial coefficient: UNCOMPILED preparation

This is a finite scalar draft, not a compiler-accepted theorem. No compiler
was launched while preparing it. The shift `j = k + 2` retains the exact
constant `1 / 24` and avoids natural subtraction at the low indices.

No measure, infinite sum, integral, or actual-source claim is made here.
-/

noncomputable section

namespace SignedJensenKernelPrep

/-- Four successive factorial recurrences, as an equality over the reals. -/
theorem factorial_four_real (n : ℕ) :
    ((n + 4).factorial : ℝ) =
      ((n : ℝ) + 4) * ((n : ℝ) + 3) * ((n : ℝ) + 2) *
        ((n : ℝ) + 1) * (n.factorial : ℝ) := by
  change (((((n + 1) + 1) + 1) + 1).factorial : ℝ) = _
  rw [Nat.factorial_succ, Nat.factorial_succ,
    Nat.factorial_succ, Nat.factorial_succ]
  push_cast
  ring

/-- The polynomial comparison underlying the exact coefficient `1 / 24`. -/
theorem fourth_factor_lower (k : ℕ) :
    12 * ((k : ℝ) + 2) * ((k : ℝ) + 1) ≤
      (2 * (k : ℝ) + 4) * (2 * (k : ℝ) + 3) *
        (2 * (k : ℝ) + 2) * (2 * (k : ℝ) + 1) := by
  have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have hquad : (3 : ℝ) ≤ (2 * (k : ℝ) + 3) * (2 * (k : ℝ) + 1) := by
    nlinarith [sq_nonneg (k : ℝ)]
  have hp : (0 : ℝ) ≤ 4 * (((k : ℝ) + 2) * ((k : ℝ) + 1)) :=
    mul_nonneg (by norm_num)
      (mul_nonneg (by linarith only [hk]) (by linarith only [hk]))
  calc
    12 * ((k : ℝ) + 2) * ((k : ℝ) + 1) =
        (4 * (((k : ℝ) + 2) * ((k : ℝ) + 1))) * 3 := by ring
    _ ≤ (4 * (((k : ℝ) + 2) * ((k : ℝ) + 1))) *
        ((2 * (k : ℝ) + 3) * (2 * (k : ℝ) + 1)) :=
      mul_le_mul_of_nonneg_left hquad hp
    _ = (2 * (k : ℝ) + 4) * (2 * (k : ℝ) + 3) *
        (2 * (k : ℝ) + 2) * (2 * (k : ℝ) + 1) := by ring

/-- For `j = k + 2`, `j(j-1)/(2(2j)!) ≤ 1/(24(2j-4)!)`. -/
theorem factorial_coefficient_shifted (k : ℕ) :
    (((k : ℝ) + 2) * ((k : ℝ) + 1)) /
        (2 * ((2 * (k + 2)).factorial : ℝ)) ≤
      1 / (24 * ((2 * k).factorial : ℝ)) := by
  have hf : (0 : ℝ) < ((2 * k).factorial : ℝ) :=
    by simpa only [Nat.cast_zero] using (Nat.cast_lt (α := ℝ)).2 (Nat.factorial_pos (2 * k))
  have hg : (0 : ℝ) < ((2 * (k + 2)).factorial : ℝ) :=
    by simpa only [Nat.cast_zero] using (Nat.cast_lt (α := ℝ)).2 (Nat.factorial_pos (2 * (k + 2)))
  have hfac : ((2 * (k + 2)).factorial : ℝ) =
      (2 * (k : ℝ) + 4) * (2 * (k : ℝ) + 3) *
        (2 * (k : ℝ) + 2) * (2 * (k : ℝ) + 1) *
          ((2 * k).factorial : ℝ) := by
    have hn : 2 * (k + 2) = 2 * k + 4 := by ring
    rw [hn, factorial_four_real]
    push_cast
    ring
  apply (div_le_div_iff₀ (mul_pos (by norm_num) hg)
    (mul_pos (by norm_num) hf)).2
  calc
    (((k : ℝ) + 2) * ((k : ℝ) + 1)) *
        (24 * ((2 * k).factorial : ℝ)) =
        (12 * ((k : ℝ) + 2) * ((k : ℝ) + 1)) *
          (2 * ((2 * k).factorial : ℝ)) := by ring
    _ ≤ ((2 * (k : ℝ) + 4) * (2 * (k : ℝ) + 3) *
        (2 * (k : ℝ) + 2) * (2 * (k : ℝ) + 1)) *
          (2 * ((2 * k).factorial : ℝ)) :=
      mul_le_mul_of_nonneg_right (fourth_factor_lower k)
        (mul_nonneg (by norm_num) (le_of_lt hf))
    _ = 1 * (2 * ((2 * (k + 2)).factorial : ℝ)) := by
      rw [hfac]
      ring

/-- The same exact coefficient comparison after division by a positive scale. -/
theorem factorial_coefficient_scaled (k : ℕ) (d : ℝ) (hd : 0 < d) :
    (((k : ℝ) + 2) * ((k : ℝ) + 1)) /
        (2 * d * ((2 * (k + 2)).factorial : ℝ)) ≤
      1 / (24 * d * ((2 * k).factorial : ℝ)) := by
  calc
    (((k : ℝ) + 2) * ((k : ℝ) + 1)) /
        (2 * d * ((2 * (k + 2)).factorial : ℝ)) =
        ((((k : ℝ) + 2) * ((k : ℝ) + 1)) /
          (2 * ((2 * (k + 2)).factorial : ℝ))) / d := by
      rw [div_div]
      congr 1 <;> ring
    _ ≤ (1 / (24 * ((2 * k).factorial : ℝ))) / d :=
      div_le_div_of_nonneg_right (factorial_coefficient_shifted k) (le_of_lt hd)
    _ = 1 / (24 * d * ((2 * k).factorial : ℝ)) := by
      rw [div_div]
      congr 1 <;> ring

/-- Equality of the factorial comparison at the first nonzero error index. -/
theorem factorial_coefficient_at_zero :
    ((2 : ℝ) * 1) / (2 * ((4 : ℕ).factorial : ℝ)) = 1 / 24 := by
  norm_num [Nat.factorial]

end SignedJensenKernelPrep



/-! Static proposed analytic join: no theorem in this draft has been compiled. -/

open scoped BigOperators

namespace SignedJensenKernelPrep

def kernelTerm (a : ℂ) (j : ℕ) : ℂ :=
  (-a) ^ j / ((2 * j).factorial : ℂ)

def completeKernel (a : ℂ) : ℂ := ∑' j : ℕ, kernelTerm a j

def finiteKernel (d : ℕ) (a : ℂ) : ℂ :=
  ∑ j ∈ Finset.range (d + 1), (SignedJensenPrep.weight d j : ℂ) * kernelTerm a j

def errorTerm (d : ℕ) (a : ℂ) (j : ℕ) : ℂ :=
  ((SignedJensenPrep.weight d j : ℂ) - 1) * kernelTerm a j

theorem kernelTerm_norm (a : ℂ) (j : ℕ) :
    ‖kernelTerm a j‖ = ‖a‖ ^ j / ((2 * j).factorial : ℝ) := by
  simp [kernelTerm, norm_div, norm_pow, Complex.norm_natCast]

theorem kernelTerm_norm_le (a : ℂ) (x : ℝ) (ha : ‖a‖ ≤ x ^ 2) (j : ℕ) :
    ‖kernelTerm a j‖ ≤ x ^ (2 * j) / ((2 * j).factorial : ℝ) := by
  rw [kernelTerm_norm]
  calc
    ‖a‖ ^ j / ((2 * j).factorial : ℝ) ≤
        (x ^ 2) ^ j / ((2 * j).factorial : ℝ) :=
      div_le_div_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg a) ha j)
        (Nat.cast_nonneg _)
    _ = _ := by rw [pow_mul]

theorem kernel_summable (a : ℂ) (x : ℝ) (ha : ‖a‖ ≤ x ^ 2) :
    Summable (kernelTerm a) :=
  (Real.hasSum_cosh x).summable.of_norm_bounded (kernelTerm_norm_le a x ha)

theorem finiteKernel_hasSum (d : ℕ) (a : ℂ) :
    HasSum (fun j : ℕ => (SignedJensenPrep.weight d j : ℂ) * kernelTerm a j)
      (finiteKernel d a) := by
  classical
  unfold finiteKernel
  apply hasSum_sum_of_ne_finset_zero
  intro j hj
  have hjnot : ¬ j < d + 1 := by simpa only [Finset.mem_range] using hj
  have hle : d + 1 ≤ j := le_of_not_gt hjnot
  have hdj : d < j := lt_of_lt_of_le (Nat.lt_succ_self d) hle
  simp [SignedJensenPrep.weight_eq_zero_of_lt hdj]

theorem errorTerm_norm (d j : ℕ) (a : ℂ) (hd : 1 ≤ d) :
    ‖errorTerm d a j‖ = (1 - SignedJensenPrep.weight d j) * ‖kernelTerm a j‖ := by
  have hw := SignedJensenPrep.weight_bounds d j hd
  have hn : ‖(SignedJensenPrep.weight d j : ℂ) - 1‖ =
      1 - SignedJensenPrep.weight d j := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr hw.2.1)]
    ring
  rw [errorTerm, norm_mul, hn]

theorem error_coefficient (d k : ℕ) (hd : 1 ≤ d) :
    (1 - SignedJensenPrep.weight d (k + 2)) /
        ((2 * (k + 2)).factorial : ℝ) ≤
      1 / (24 * (d : ℝ) * ((2 * k).factorial : ℝ)) := by
  have hdpos : (0 : ℝ) < (d : ℝ) :=
    by simpa only [Nat.cast_zero] using (Nat.cast_lt (α := ℝ)).2 (lt_of_lt_of_le Nat.zero_lt_one hd)
  have hw := (SignedJensenPrep.weight_bounds d (k + 2) hd).2.2
  have hh : 1 - SignedJensenPrep.weight d (k + 2) ≤
      (((k : ℝ) + 2) * ((k : ℝ) + 1)) / (2 * (d : ℝ)) := by
    convert hw using 1 <;> push_cast <;> ring
  calc
    (1 - SignedJensenPrep.weight d (k + 2)) /
        ((2 * (k + 2)).factorial : ℝ) ≤
      ((((k : ℝ) + 2) * ((k : ℝ) + 1)) / (2 * (d : ℝ))) /
        ((2 * (k + 2)).factorial : ℝ) :=
      div_le_div_of_nonneg_right hh (Nat.cast_nonneg _)
    _ = (((k : ℝ) + 2) * ((k : ℝ) + 1)) /
        (2 * (d : ℝ) * ((2 * (k + 2)).factorial : ℝ)) := by rw [div_div]
    _ ≤ _ := factorial_coefficient_scaled k (d : ℝ) hdpos

theorem shifted_error_bound (d k : ℕ) (hd : 1 ≤ d)
    (a : ℂ) (x : ℝ) (hx : 0 ≤ x) (ha : ‖a‖ ≤ x ^ 2) :
    ‖errorTerm d a (k + 2)‖ ≤
      x ^ 4 / (24 * (d : ℝ)) * (x ^ (2 * k) / ((2 * k).factorial : ℝ)) := by
  have hw := SignedJensenPrep.weight_bounds d (k + 2) hd
  rw [errorTerm_norm d (k + 2) a hd]
  calc
    (1 - SignedJensenPrep.weight d (k + 2)) * ‖kernelTerm a (k + 2)‖ ≤
        (1 - SignedJensenPrep.weight d (k + 2)) *
          (x ^ (2 * (k + 2)) / ((2 * (k + 2)).factorial : ℝ)) :=
      mul_le_mul_of_nonneg_left (kernelTerm_norm_le a x ha (k + 2))
        (sub_nonneg.mpr hw.2.1)
    _ = ((1 - SignedJensenPrep.weight d (k + 2)) /
        ((2 * (k + 2)).factorial : ℝ)) * x ^ (2 * (k + 2)) := by ring
    _ ≤ (1 / (24 * (d : ℝ) * ((2 * k).factorial : ℝ))) *
        x ^ (2 * (k + 2)) :=
      mul_le_mul_of_nonneg_right (error_coefficient d k hd) (pow_nonneg hx _)
    _ = _ := by
      have hn : 2 * (k + 2) = 2 * k + 4 := by ring
      rw [hn, pow_add]
      ring

theorem finite_prefix_bound (d n : ℕ) (hd : 1 ≤ d)
    (a : ℂ) (x : ℝ) (hx : 0 ≤ x) (ha : ‖a‖ ≤ x ^ 2) :
    ‖∑ k ∈ Finset.range n, errorTerm d a (k + 2)‖ ≤
      x ^ 4 / (24 * (d : ℝ)) *
        ∑ k ∈ Finset.range n, x ^ (2 * k) / ((2 * k).factorial : ℝ) := by
  calc
    ‖∑ k ∈ Finset.range n, errorTerm d a (k + 2)‖ ≤
        ∑ k ∈ Finset.range n, x ^ 4 / (24 * (d : ℝ)) *
          (x ^ (2 * k) / ((2 * k).factorial : ℝ)) :=
      norm_sum_le_of_le _ (fun k _ => shifted_error_bound d k hd a x hx ha)
    _ = _ := by rw [Finset.mul_sum]

theorem kernel_error_hasSum (d : ℕ) (hd : 1 ≤ d)
    (a : ℂ) (x : ℝ) (ha : ‖a‖ ≤ x ^ 2) :
    HasSum (fun k : ℕ => errorTerm d a (k + 2))
      (finiteKernel d a - completeKernel a) := by
  have hc : HasSum (kernelTerm a) (completeKernel a) :=
    (kernel_summable a x ha).hasSum
  have herr : HasSum (errorTerm d a) (finiteKernel d a - completeKernel a) := by
    convert (finiteKernel_hasSum d a).sub hc using 1
    funext j
    dsimp [errorTerm]
    ring
  have hzero : errorTerm d a 0 = 0 := by
    simp [errorTerm, SignedJensenPrep.weight_zero]
  have hone : errorTerm d a 1 = 0 := by
    simp [errorTerm, SignedJensenPrep.weight_one d hd]
  have hhead : ∑ j ∈ Finset.range 2, errorTerm d a j = 0 := by
    simp [Finset.sum_range_succ, hzero, hone]
  have hshift := (hasSum_nat_add_iff' (f := errorTerm d a) 2).mpr herr
  simpa only [hhead, sub_zero] using hshift

theorem pointwise_kernel_aux (d : ℕ) (hd : 1 ≤ d)
    (a : ℂ) (x : ℝ) (hx : 0 ≤ x) (ha : ‖a‖ ≤ x ^ 2) :
    ‖finiteKernel d a - completeKernel a‖ ≤
      x ^ 4 / (24 * (d : ℝ)) * Real.cosh x := by
  have he := kernel_error_hasSum d hd a x ha
  have hm := (Real.hasSum_cosh x).mul_left (x ^ 4 / (24 * (d : ℝ)))
  exact he.norm_le_of_bounded hm (fun k => shifted_error_bound d k hd a x hx ha)

theorem kernelTerm_native (z : ℂ) (u : ℝ) (j : ℕ) :
    kernelTerm (z * (u : ℂ) ^ 2) j =
      (-1 : ℂ) ^ j * z ^ j * (u : ℂ) ^ (2 * j) /
        ((2 * j).factorial : ℂ) := by
  have hneg : -(z * (u : ℂ) ^ 2) = ((-1 : ℂ) * z) * (u : ℂ) ^ 2 := by ring
  rw [kernelTerm, hneg]
  simp only [mul_pow, pow_mul]

theorem pointwise_kernel_disk (d : ℕ) (hd : 1 ≤ d)
    (z : ℂ) (u r : ℝ) (hu : 0 ≤ u) (hr : 0 ≤ r) (hz : ‖z‖ ≤ r) :
    ‖finiteKernel d (z * (u : ℂ) ^ 2) - completeKernel (z * (u : ℂ) ^ 2)‖ ≤
      (r ^ 2 * u ^ 4) / (24 * (d : ℝ)) * Real.cosh (Real.sqrt r * u) := by
  have hx : 0 ≤ Real.sqrt r * u := mul_nonneg (Real.sqrt_nonneg r) hu
  have ha : ‖z * (u : ℂ) ^ 2‖ ≤ (Real.sqrt r * u) ^ 2 := by
    rw [norm_mul, norm_pow, Complex.norm_of_nonneg hu]
    calc
      ‖z‖ * u ^ 2 ≤ r * u ^ 2 := mul_le_mul_of_nonneg_right hz (sq_nonneg u)
      _ = (Real.sqrt r * u) ^ 2 := by rw [mul_pow, Real.sq_sqrt hr]
  have hfour : (Real.sqrt r * u) ^ 4 = r ^ 2 * u ^ 4 := by
    rw [mul_pow]
    have hs : Real.sqrt r ^ 4 = (Real.sqrt r ^ 2) ^ 2 := by ring
    rw [hs, Real.sq_sqrt hr]
  have h := pointwise_kernel_aux d hd (z * (u : ℂ) ^ 2) (Real.sqrt r * u) hx ha
  simpa only [hfour] using h

end SignedJensenKernelPrep

#print axioms SignedJensenKernelPrep.factorial_coefficient_shifted
#print axioms SignedJensenKernelPrep.factorial_coefficient_at_zero
#print axioms SignedJensenKernelPrep.error_coefficient
#print axioms SignedJensenKernelPrep.finite_prefix_bound
#print axioms SignedJensenKernelPrep.kernel_summable
#print axioms SignedJensenKernelPrep.finiteKernel_hasSum
#print axioms SignedJensenKernelPrep.kernel_error_hasSum
#print axioms SignedJensenKernelPrep.kernelTerm_native
#print axioms SignedJensenKernelPrep.pointwise_kernel_aux
#print axioms SignedJensenKernelPrep.pointwise_kernel_disk
