# Exact package-owned statements and hypotheses

These are the accepted source headers, with proof introductions omitted. Context: `open scoped BigOperators`, namespace `CumulativeQuadratic`, and `variable {R : Type*} [CommRing R]`. The arrays and coefficients are natural-indexed functions; nodes use `i ≤ n`, `j ≤ m`, while mixed cells use `i < n`, `j < m`. The totals are `prefixSum u (n+1)` and `prefixSum v (m+1)`. Zero side lengths are permitted.

Definitions in [CumulativeQuadratic.lean](CumulativeQuadratic.lean): `prefixSum u k = ∑ i ∈ Finset.range k, u i`; `mixedDifference A i j = (A (i+1) (j+1) - A i (j+1)) - (A (i+1) j - A i j)`.

The three headline statements are `mixedDifference_eq_iff_boundary_difference`, `eq_of_mixedDifference_eq_of_boundary_eq`, and `bilinear_eq_of_mixedDifference_eq_of_mass_zero`. All eleven package-owned public theorem headers follow, including the supporting Abel identities. Imported Mathlib declarations and the private helper are not listed as package-owned public API. The symmetric `quadratic_cumulative` requires the displayed `hA`; its zero-mass counterpart has no symmetry hypothesis.

## `mixedDifference_eq`

[CumulativeQuadratic.lean, line 27](CumulativeQuadratic.lean#L27)

```lean
theorem mixedDifference_eq (A : ℕ → ℕ → R) (i j : ℕ) :
    mixedDifference A i j =
      A i j - A (i + 1) j - A i (j + 1) + A (i + 1) (j + 1)
```

## `bilinear_cumulative`

[CumulativeQuadratic.lean, line 35](CumulativeQuadratic.lean#L35)

```lean
theorem bilinear_cumulative (u v : ℕ → R) (A : ℕ → ℕ → R) (n m : ℕ) :
    (∑ a ∈ Finset.range (n + 1), ∑ b ∈ Finset.range (m + 1), u a * A a b * v b) =
      prefixSum u (n + 1) * prefixSum v (m + 1) * A n m -
        prefixSum v (m + 1) *
          (∑ i ∈ Finset.range n, prefixSum u (i + 1) * (A (i + 1) m - A i m)) -
        prefixSum u (n + 1) *
          (∑ j ∈ Finset.range m, prefixSum v (j + 1) * (A n (j + 1) - A n j)) +
        ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range m,
          prefixSum u (i + 1) * prefixSum v (j + 1) * mixedDifference A i j
```

## `quadratic_cumulative`

[CumulativeQuadratic.lean, line 103](CumulativeQuadratic.lean#L103)

```lean
theorem quadratic_cumulative (u : ℕ → R) (A : ℕ → ℕ → R) (n : ℕ)
    (hA : ∀ i ≤ n, ∀ j ≤ n, A i j = A j i) :
    (∑ a ∈ Finset.range (n + 1), ∑ b ∈ Finset.range (n + 1), u a * A a b * u b) =
      prefixSum u (n + 1) ^ 2 * A n n -
        2 * prefixSum u (n + 1) *
          (∑ i ∈ Finset.range n, prefixSum u (i + 1) * (A (i + 1) n - A i n)) +
        ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
          prefixSum u (i + 1) * prefixSum u (j + 1) * mixedDifference A i j
```

## `quadratic_cumulative_of_mass_zero`

[CumulativeQuadratic.lean, line 126](CumulativeQuadratic.lean#L126)

```lean
theorem quadratic_cumulative_of_mass_zero (u : ℕ → R) (A : ℕ → ℕ → R) (n : ℕ)
    (hmass : prefixSum u (n + 1) = 0) :
    (∑ a ∈ Finset.range (n + 1), ∑ b ∈ Finset.range (n + 1), u a * A a b * u b) =
      ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
        prefixSum u (i + 1) * prefixSum u (j + 1) * mixedDifference A i j
```

## `eq_row_add_column_sub_of_mixedDifference_eq_zero`

[CumulativeBoundary.lean, line 52](CumulativeBoundary.lean#L52)

```lean
theorem eq_row_add_column_sub_of_mixedDifference_eq_zero
    (A : ℕ → ℕ → R) (n m : ℕ)
    (h : ∀ a < n, ∀ b < m, mixedDifference A a b = 0)
    {i j : ℕ} (hi : i ≤ n) (hj : j ≤ m) :
    A i j = A i m + A n j - A n m
```

## `mixedDifference_eq_zero_iff_boundary_decomposition`

[CumulativeBoundary.lean, line 65](CumulativeBoundary.lean#L65)

```lean
theorem mixedDifference_eq_zero_iff_boundary_decomposition
    (A : ℕ → ℕ → R) (n m : ℕ) :
    (∀ i < n, ∀ j < m, mixedDifference A i j = 0) ↔
      ∀ i ≤ n, ∀ j ≤ m, A i j = A i m + A n j - A n m
```

## `mixedDifference_eq_iff_boundary_difference`

[CumulativeBoundary.lean, line 86](CumulativeBoundary.lean#L86)

```lean
theorem mixedDifference_eq_iff_boundary_difference
    (A B : ℕ → ℕ → R) (n m : ℕ) :
    (∀ i < n, ∀ j < m, mixedDifference A i j = mixedDifference B i j) ↔
      ∀ i ≤ n, ∀ j ≤ m,
        A i j - B i j = (A i m - B i m) + (A n j - B n j) -
          (A n m - B n m)
```

## `eq_of_mixedDifference_eq_of_boundary_eq`

[CumulativeBoundary.lean, line 113](CumulativeBoundary.lean#L113)

```lean
theorem eq_of_mixedDifference_eq_of_boundary_eq
    (A B : ℕ → ℕ → R) (n m : ℕ)
    (hD : ∀ a < n, ∀ b < m, mixedDifference A a b = mixedDifference B a b)
    (hrow : ∀ b ≤ m, A n b = B n b)
    (hcolumn : ∀ a ≤ n, A a m = B a m)
    {i j : ℕ} (hi : i ≤ n) (hj : j ≤ m) :
    A i j = B i j
```

## `mixedDifference_add_row_column`

[CumulativeBoundary.lean, line 128](CumulativeBoundary.lean#L128)

```lean
theorem mixedDifference_add_row_column
    (A : ℕ → ℕ → R) (p q : ℕ → R) (c : R) (i j : ℕ) :
    mixedDifference (fun a b => A a b + p a + q b + c) i j =
      mixedDifference A i j
```

## `bilinear_cumulative_of_mixedDifference_eq_zero`

[CumulativeBoundary.lean, line 138](CumulativeBoundary.lean#L138)

```lean
theorem bilinear_cumulative_of_mixedDifference_eq_zero
    (u v : ℕ → R) (A : ℕ → ℕ → R) (n m : ℕ)
    (hD : ∀ i < n, ∀ j < m, mixedDifference A i j = 0) :
    (∑ a ∈ Finset.range (n + 1), ∑ b ∈ Finset.range (m + 1), u a * A a b * v b) =
      prefixSum u (n + 1) * prefixSum v (m + 1) * A n m -
        prefixSum v (m + 1) *
          (∑ i ∈ Finset.range n, prefixSum u (i + 1) * (A (i + 1) m - A i m)) -
        prefixSum u (n + 1) *
          (∑ j ∈ Finset.range m, prefixSum v (j + 1) * (A n (j + 1) - A n j))
```

## `bilinear_eq_of_mixedDifference_eq_of_mass_zero`

[CumulativeBoundary.lean, line 160](CumulativeBoundary.lean#L160)

```lean
theorem bilinear_eq_of_mixedDifference_eq_of_mass_zero
    (u v : ℕ → R) (A B : ℕ → ℕ → R) (n m : ℕ)
    (hu : prefixSum u (n + 1) = 0) (hv : prefixSum v (m + 1) = 0)
    (hD : ∀ i < n, ∀ j < m, mixedDifference A i j = mixedDifference B i j) :
    (∑ a ∈ Finset.range (n + 1), ∑ b ∈ Finset.range (m + 1), u a * A a b * v b) =
      ∑ a ∈ Finset.range (n + 1), ∑ b ∈ Finset.range (m + 1), u a * B a b * v b
```
