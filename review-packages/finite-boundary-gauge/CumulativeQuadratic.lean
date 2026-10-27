import Mathlib.Algebra.BigOperators.Module
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

/-!
# Finite cumulative transforms of bilinear and quadratic sums

An iterated application of `Finset.sum_range_by_parts'`, retaining both
boundary sums and the corner mass term. The symmetric specialization
reconstructs SEQUENTIAL-072's written identity for arbitrary coefficients.
No zero-mass, positivity, regularity, arithmetic or RH assumption is used.
-/

open scoped BigOperators

namespace CumulativeQuadratic

variable {R : Type*} [CommRing R]

/-- The sum of the first `n` coefficients, before index `n`. -/
def prefixSum (u : ℕ → R) (n : ℕ) : R := ∑ i ∈ Finset.range n, u i

/-- The forward mixed difference in both kernel coordinates. -/
def mixedDifference (A : ℕ → ℕ → R) (i j : ℕ) : R :=
  (A (i + 1) (j + 1) - A i (j + 1)) - (A (i + 1) j - A i j)

theorem mixedDifference_eq (A : ℕ → ℕ → R) (i j : ℕ) :
    mixedDifference A i j =
      A i j - A (i + 1) j - A i (j + 1) + A (i + 1) (j + 1) := by
  unfold mixedDifference
  ring

/-- Two-variable Abel summation for a rectangular kernel, with arbitrary
coefficients and both (possibly nonzero) total masses. -/
theorem bilinear_cumulative (u v : ℕ → R) (A : ℕ → ℕ → R) (n m : ℕ) :
    (∑ a ∈ Finset.range (n + 1), ∑ b ∈ Finset.range (m + 1), u a * A a b * v b) =
      prefixSum u (n + 1) * prefixSum v (m + 1) * A n m -
        prefixSum v (m + 1) *
          (∑ i ∈ Finset.range n, prefixSum u (i + 1) * (A (i + 1) m - A i m)) -
        prefixSum u (n + 1) *
          (∑ j ∈ Finset.range m, prefixSum v (j + 1) * (A n (j + 1) - A n j)) +
        ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range m,
          prefixSum u (i + 1) * prefixSum v (j + 1) * mixedDifference A i j := by
  have hab (f g : ℕ → R) (k : ℕ) :
      (∑ i ∈ Finset.range (k + 1), f i * g i) =
        prefixSum f (k + 1) * g k -
          ∑ i ∈ Finset.range k, prefixSum f (i + 1) * (g (i + 1) - g i) := by
    simpa only [prefixSum, smul_eq_mul, Nat.add_sub_cancel] using
      (Finset.sum_range_by_parts' f g (k + 1))
  let W : ℕ → R := fun a => ∑ b ∈ Finset.range (m + 1), v b * A a b
  have hWn : W n = prefixSum v (m + 1) * A n m -
      ∑ j ∈ Finset.range m, prefixSum v (j + 1) * (A n (j + 1) - A n j) := by
    exact hab v (A n) m
  have hWdiff (i : ℕ) : W (i + 1) - W i =
      ∑ b ∈ Finset.range (m + 1), v b * (A (i + 1) b - A i b) := by
    simp only [W, mul_sub, Finset.sum_sub_distrib]
  have hWd (i : ℕ) : W (i + 1) - W i =
      prefixSum v (m + 1) * (A (i + 1) m - A i m) -
        ∑ j ∈ Finset.range m, prefixSum v (j + 1) * mixedDifference A i j := by
    rw [hWdiff]
    exact hab v (fun b => A (i + 1) b - A i b) m
  have hS :
      (∑ a ∈ Finset.range (n + 1), ∑ b ∈ Finset.range (m + 1), u a * A a b * v b) =
        ∑ a ∈ Finset.range (n + 1), u a * W a := by
    apply Finset.sum_congr rfl
    intro a ha
    dsimp only [W]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b hb
    ring
  have hboundary :
      (∑ i ∈ Finset.range n,
        prefixSum u (i + 1) * (prefixSum v (m + 1) * (A (i + 1) m - A i m))) =
        prefixSum v (m + 1) *
          ∑ i ∈ Finset.range n, prefixSum u (i + 1) * (A (i + 1) m - A i m) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hmixed :
      (∑ i ∈ Finset.range n, prefixSum u (i + 1) *
        (∑ j ∈ Finset.range m, prefixSum v (j + 1) * mixedDifference A i j)) =
        ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range m,
          prefixSum u (i + 1) * prefixSum v (j + 1) * mixedDifference A i j := by
    simp_rw [Finset.mul_sum, mul_assoc]
  have hsplit :
      (∑ i ∈ Finset.range n, prefixSum u (i + 1) *
        (prefixSum v (m + 1) * (A (i + 1) m - A i m) -
          ∑ j ∈ Finset.range m, prefixSum v (j + 1) * mixedDifference A i j)) =
        (∑ i ∈ Finset.range n,
          prefixSum u (i + 1) * (prefixSum v (m + 1) * (A (i + 1) m - A i m))) -
        ∑ i ∈ Finset.range n, prefixSum u (i + 1) *
          (∑ j ∈ Finset.range m, prefixSum v (j + 1) * mixedDifference A i j) := by
    simp only [mul_sub, Finset.sum_sub_distrib]
  rw [hS, hab, hWn]
  simp_rw [hWd]
  rw [hsplit, hboundary, hmixed]
  ring

/-- The mass-sensitive symmetric quadratic identity of SEQUENTIAL-072.
Symmetry is required only on the finite matrix actually being summed. -/
theorem quadratic_cumulative (u : ℕ → R) (A : ℕ → ℕ → R) (n : ℕ)
    (hA : ∀ i ≤ n, ∀ j ≤ n, A i j = A j i) :
    (∑ a ∈ Finset.range (n + 1), ∑ b ∈ Finset.range (n + 1), u a * A a b * u b) =
      prefixSum u (n + 1) ^ 2 * A n n -
        2 * prefixSum u (n + 1) *
          (∑ i ∈ Finset.range n, prefixSum u (i + 1) * (A (i + 1) n - A i n)) +
        ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
          prefixSum u (i + 1) * prefixSum u (j + 1) * mixedDifference A i j := by
  have hcross :
      (∑ j ∈ Finset.range n, prefixSum u (j + 1) * (A n (j + 1) - A n j)) =
        ∑ i ∈ Finset.range n, prefixSum u (i + 1) * (A (i + 1) n - A i n) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hjn : j ≤ n := Nat.le_of_lt (Finset.mem_range.mp hj)
    have hs : j + 1 ≤ n := Nat.succ_le_of_lt (Finset.mem_range.mp hj)
    rw [hA n le_rfl (j + 1) hs, hA n le_rfl j hjn]
  have h := bilinear_cumulative u u A n n
  rw [hcross] at h
  calc
    _ = _ := h
    _ = _ := by ring

/-- With zero total mass only the mixed-difference part remains. -/
theorem quadratic_cumulative_of_mass_zero (u : ℕ → R) (A : ℕ → ℕ → R) (n : ℕ)
    (hmass : prefixSum u (n + 1) = 0) :
    (∑ a ∈ Finset.range (n + 1), ∑ b ∈ Finset.range (n + 1), u a * A a b * u b) =
      ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
        prefixSum u (i + 1) * prefixSum u (j + 1) * mixedDifference A i j := by
  simpa only [hmass, zero_mul, sub_zero, zero_sub, add_zero, zero_add] using
    (bilinear_cumulative u u A n n)

/- The one-coordinate checks instantiate the actual exported theorem.
They deliberately retain nonzero masses and a nonzero corner entry. -/
example (u v : ℕ → R) (A : ℕ → ℕ → R) :
    (∑ a ∈ Finset.range 1, ∑ b ∈ Finset.range 1, u a * A a b * v b) =
      prefixSum u 1 * prefixSum v 1 * A 0 0 := by
  simpa only [Nat.zero_add, Finset.sum_range_zero, zero_mul, mul_zero,
    sub_zero, add_zero] using (bilinear_cumulative u v A 0 0)

end CumulativeQuadratic

#print axioms CumulativeQuadratic.bilinear_cumulative
#print axioms CumulativeQuadratic.quadratic_cumulative
#print axioms CumulativeQuadratic.quadratic_cumulative_of_mass_zero
