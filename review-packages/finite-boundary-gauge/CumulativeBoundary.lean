import CumulativeQuadratic
import Mathlib.Tactic.LinearCombination

/-!
# Finite mixed differences determine a kernel up to its boundary

This finite extension uses the accepted definitions in
`CumulativeQuadratic`. It does not repeat the accepted Abel proof.
The new target is the finite-box kernel of the mixed-difference map:
zero mixed difference is exactly row-plus-column separability, and mixed
differences together with a final row and column determine the kernel.

The corner is subtracted once in the boundary reconstruction. All statements
allow arbitrary commutative rings, arbitrary kernels, and zero side lengths.
The collection verification receipt records compilation and terminal axiom checks.
-/

open scoped BigOperators

namespace CumulativeQuadratic

variable {R : Type*} [CommRing R]

private theorem eq_origin_of_mixedDifference_eq_zero
    (A : ℕ → ℕ → R) (n m : ℕ)
    (h : ∀ i < n, ∀ j < m, mixedDifference A i j = 0) :
    ∀ i ≤ n, ∀ j ≤ m, A i j = A i 0 + A 0 j - A 0 0 := by
  intro i
  induction i with
  | zero =>
      intro _ j _
      ring
  | succ i ih =>
      intro hi j
      induction j with
      | zero =>
          intro _
          ring
      | succ j ihj =>
          intro hj
          have hin : i < n := Nat.lt_of_succ_le hi
          have hjm : j < m := Nat.lt_of_succ_le hj
          have hcell := h i hin j hjm
          dsimp only [mixedDifference] at hcell
          have hleft := ih (Nat.le_of_lt hin) (j + 1) hj
          have hdown := ihj (Nat.le_of_lt hjm)
          have hdiag := ih (Nat.le_of_lt hin) j (Nat.le_of_lt hjm)
          linear_combination hcell + hleft + hdown - hdiag

/-- A kernel with zero mixed differences is reconstructed from the final
row and column, with the common corner subtracted once. -/
theorem eq_row_add_column_sub_of_mixedDifference_eq_zero
    (A : ℕ → ℕ → R) (n m : ℕ)
    (h : ∀ a < n, ∀ b < m, mixedDifference A a b = 0)
    {i j : ℕ} (hi : i ≤ n) (hj : j ≤ m) :
    A i j = A i m + A n j - A n m := by
  have hij := eq_origin_of_mixedDifference_eq_zero A n m h i hi j hj
  have him := eq_origin_of_mixedDifference_eq_zero A n m h i hi m le_rfl
  have hnj := eq_origin_of_mixedDifference_eq_zero A n m h n le_rfl j hj
  have hnm := eq_origin_of_mixedDifference_eq_zero A n m h n le_rfl m le_rfl
  linear_combination hij - him - hnj + hnm

/-- On a finite rectangle, vanishing mixed difference is equivalent to
the exact final-row/final-column decomposition. -/
theorem mixedDifference_eq_zero_iff_boundary_decomposition
    (A : ℕ → ℕ → R) (n m : ℕ) :
    (∀ i < n, ∀ j < m, mixedDifference A i j = 0) ↔
      ∀ i ≤ n, ∀ j ≤ m, A i j = A i m + A n j - A n m := by
  constructor
  · intro h i hi j hj
    exact eq_row_add_column_sub_of_mixedDifference_eq_zero A n m h hi hj
  · intro h i hi j hj
    have hi0 : i ≤ n := Nat.le_of_lt hi
    have hj0 : j ≤ m := Nat.le_of_lt hj
    have hi1 : i + 1 ≤ n := Nat.succ_le_of_lt hi
    have hj1 : j + 1 ≤ m := Nat.succ_le_of_lt hj
    have h11 := h (i + 1) hi1 (j + 1) hj1
    have h01 := h i hi0 (j + 1) hj1
    have h10 := h (i + 1) hi1 j hj0
    have h00 := h i hi0 j hj0
    dsimp only [mixedDifference]
    linear_combination h11 - h01 - h10 + h00

/-- Equal mixed differences mean that the difference of the two kernels
is exactly its row-plus-column boundary gauge. -/
theorem mixedDifference_eq_iff_boundary_difference
    (A B : ℕ → ℕ → R) (n m : ℕ) :
    (∀ i < n, ∀ j < m, mixedDifference A i j = mixedDifference B i j) ↔
      ∀ i ≤ n, ∀ j ≤ m,
        A i j - B i j = (A i m - B i m) + (A n j - B n j) -
          (A n m - B n m) := by
  let C : ℕ → ℕ → R := fun i j => A i j - B i j
  constructor
  · intro h i hi j hj
    have hC : ∀ a < n, ∀ b < m, mixedDifference C a b = 0 := by
      intro a ha b hb
      have hab := h a ha b hb
      dsimp only [mixedDifference] at hab
      dsimp only [mixedDifference, C]
      linear_combination hab
    exact eq_row_add_column_sub_of_mixedDifference_eq_zero C n m hC hi hj
  · intro h i hi j hj
    have hC : ∀ a ≤ n, ∀ b ≤ m, C a b = C a m + C n b - C n m := h
    have hz := (mixedDifference_eq_zero_iff_boundary_decomposition C n m).mpr hC
      i hi j hj
    dsimp only [mixedDifference, C] at hz
    dsimp only [mixedDifference]
    linear_combination hz

/-- Equal mixed differences and equal final row and column determine
every entry on the finite rectangle. The two boundary requirements retain
the shared corner rather than silently discarding it. -/
theorem eq_of_mixedDifference_eq_of_boundary_eq
    (A B : ℕ → ℕ → R) (n m : ℕ)
    (hD : ∀ a < n, ∀ b < m, mixedDifference A a b = mixedDifference B a b)
    (hrow : ∀ b ≤ m, A n b = B n b)
    (hcolumn : ∀ a ≤ n, A a m = B a m)
    {i j : ℕ} (hi : i ≤ n) (hj : j ≤ m) :
    A i j = B i j := by
  have h := (mixedDifference_eq_iff_boundary_difference A B n m).mp hD i hi j hj
  have hcol := hcolumn i hi
  have hrowj := hrow j hj
  have hcorner := hrow m le_rfl
  linear_combination h + hcol + hrowj - hcorner

/-- Adding an arbitrary row term, column term and constant changes no
mixed difference. This is the forward direction of the gauge principle. -/
theorem mixedDifference_add_row_column
    (A : ℕ → ℕ → R) (p q : ℕ → R) (c : R) (i j : ℕ) :
    mixedDifference (fun a b => A a b + p a + q b + c) i j =
      mixedDifference A i j := by
  unfold mixedDifference
  ring

/-- Application of the accepted Abel identity: a zero-mixed-difference
kernel still has its corner and both independent boundary sums. This is a
supporting corollary, not the new kernel characterization above. -/
theorem bilinear_cumulative_of_mixedDifference_eq_zero
    (u v : ℕ → R) (A : ℕ → ℕ → R) (n m : ℕ)
    (hD : ∀ i < n, ∀ j < m, mixedDifference A i j = 0) :
    (∑ a ∈ Finset.range (n + 1), ∑ b ∈ Finset.range (m + 1), u a * A a b * v b) =
      prefixSum u (n + 1) * prefixSum v (m + 1) * A n m -
        prefixSum v (m + 1) *
          (∑ i ∈ Finset.range n, prefixSum u (i + 1) * (A (i + 1) m - A i m)) -
        prefixSum u (n + 1) *
          (∑ j ∈ Finset.range m, prefixSum v (j + 1) * (A n (j + 1) - A n j)) := by
  have hzero :
      (∑ i ∈ Finset.range n, ∑ j ∈ Finset.range m,
        prefixSum u (i + 1) * prefixSum v (j + 1) * mixedDifference A i j) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    apply Finset.sum_eq_zero
    intro j hj
    rw [hD i (Finset.mem_range.mp hi) j (Finset.mem_range.mp hj), mul_zero]
  simpa only [hzero, add_zero] using bilinear_cumulative u v A n m

/-- Equal mixed differences give the same bilinear pairing when both
coefficient lists have zero total mass. Both mass hypotheses are explicit;
without them the preceding corner and edge terms must be retained. -/
theorem bilinear_eq_of_mixedDifference_eq_of_mass_zero
    (u v : ℕ → R) (A B : ℕ → ℕ → R) (n m : ℕ)
    (hu : prefixSum u (n + 1) = 0) (hv : prefixSum v (m + 1) = 0)
    (hD : ∀ i < n, ∀ j < m, mixedDifference A i j = mixedDifference B i j) :
    (∑ a ∈ Finset.range (n + 1), ∑ b ∈ Finset.range (m + 1), u a * A a b * v b) =
      ∑ a ∈ Finset.range (n + 1), ∑ b ∈ Finset.range (m + 1), u a * B a b * v b := by
  have hA := bilinear_cumulative u v A n m
  have hB := bilinear_cumulative u v B n m
  simp only [hu, hv, zero_mul, sub_zero, zero_sub, add_zero, zero_add] at hA hB
  rw [hA, hB]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [hD i (Finset.mem_range.mp hi) j (Finset.mem_range.mp hj)]

/- Small exact boundary regression checks.
The one-coordinate case has no mixed cells, so only the corner remains. -/
example (A B : ℕ → ℕ → R) (h : A 0 0 = B 0 0) : A 0 0 = B 0 0 := by
  apply eq_of_mixedDifference_eq_of_boundary_eq A B 0 0
  · intro i hi
    exact (Nat.not_lt_zero i hi).elim
  · intro j hj
    have : j = 0 := Nat.eq_zero_of_le_zero hj
    simpa only [this] using h
  · intro i hi
    have : i = 0 := Nat.eq_zero_of_le_zero hi
    simpa only [this] using h
  · exact le_rfl
  · exact le_rfl

example (c : R) :
    (fun i j : ℕ => c) 0 0 =
      (fun i j : ℕ => c) 0 1 + (fun i j : ℕ => c) 1 0 -
        (fun i j : ℕ => c) 1 1 := by
  ring

end CumulativeQuadratic

#print axioms CumulativeQuadratic.eq_row_add_column_sub_of_mixedDifference_eq_zero
#print axioms CumulativeQuadratic.mixedDifference_eq_zero_iff_boundary_decomposition
#print axioms CumulativeQuadratic.mixedDifference_eq_iff_boundary_difference
#print axioms CumulativeQuadratic.eq_of_mixedDifference_eq_of_boundary_eq
#print axioms CumulativeQuadratic.mixedDifference_add_row_column
#print axioms CumulativeQuadratic.bilinear_cumulative_of_mixedDifference_eq_zero
#print axioms CumulativeQuadratic.bilinear_eq_of_mixedDifference_eq_of_mass_zero
