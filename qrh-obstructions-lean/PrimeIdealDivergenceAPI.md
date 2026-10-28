# Selected prime-ideal divergence API

This is a selection of four supporting lemmas from the `PrimeIdealDivergence` namespace in [Obstructions.lean](Obstructions.lean), not a roster of every declaration in that namespace. The types below retain the source's number-field parameters, finite exclusion, fixed norm cutoff and nested subtype projections.

## Shared parameters and definitions

```lean
open scoped Topology nonZeroDivisors
open Filter UniqueFactorizationMonoid

namespace PrimeIdealDivergence

variable (K : Type*) [Field K] [NumberField K]

abbrev NZIdeal := (Ideal (NumberField.RingOfIntegers K))⁰
abbrev PrimeIdeal := {I : Ideal (NumberField.RingOfIntegers K) // Prime I}

def normI (I : Ideal (NumberField.RingOfIntegers K)) : ℝ :=
  (Ideal.absNorm I : ℝ)
```

`NZIdeal K` uses the multiplicative non-zero-divisor submonoid of ideals. `PrimeIdeal K` uses the multiplicative-monoid predicate `Prime I`, which excludes zero and units. In this setting it indexes the intended nonzero prime ideals of the ring of integers. It is not a type of prime elements of the number field or its ring of integers.

`normI` is the natural absolute ideal norm cast to ℝ. The proof works through exact factorization of ideals, not element unique factorization. It does not require class number one. The typeclass assumptions are exactly `[Field K] [NumberField K]`.

## All nonzero ideal reciprocals

```lean
lemma ideal_reciprocals_not_summable :
    ¬ Summable (fun I : NZIdeal K => 1 / normI K I.val)
```

This is the supporting nonsummability statement for nonzero ideals. The proof uses dominated convergence and the existing ideal-count asymptotic with nonzero Dedekind-zeta residue.

## Prime-ideal reciprocals

```lean
lemma prime_reciprocals_not_summable :
    ¬ Summable (fun p : PrimeIdeal K => 1 / normI K p.val)
```

The proof derives a contradiction from hypothetical prime-reciprocal summability: positive prime-power sums and finite products would then control all ideal reciprocals through an injective exact factorization map.

## Finite exclusions and the fixed norm tail

```lean
lemma prime_tail_reciprocals_not_summable
    (S : Set (PrimeIdeal K)) (hS : S.Finite) :
    ¬ Summable (fun p : {p : PrimeIdeal K // p ∉ S ∧ 64 ≤ normI K p.val} =>
      1 / normI K p.val.val)
```

The exclusion S is an arbitrary finite set of prime ideals. The norm cutoff is the fixed real threshold 64, including equality. Finiteness of the norm-bounded ideal family makes the removed small-norm portion finite. The displayed theorem does not quantify over a general replacement cutoff.

The outer subtype records both tail conditions. Its `p.val` is a `PrimeIdeal K`; `p.val.val` is the underlying ideal. Those projections have different types and are retained in the exact statement.

## Unbounded finite subsums

```lean
lemma prime_tail_reciprocals_unbounded
    (S : Set (PrimeIdeal K)) (hS : S.Finite) :
    ∀ B : ℝ, ∃ s : Finset {p : PrimeIdeal K // p ∉ S ∧ 64 ≤ normI K p.val},
      B < ∑ p ∈ s, 1 / normI K p.val.val

end PrimeIdealDivergence
```

This last conclusion is an explicit `∀ B, ∃ Finset` statement for the nonnegative reciprocal family. It does not choose a prime enumeration, give a quantitative growth rate, or export a separate norm-ordered partial-sum limit theorem. Lean's real `tsum` is totalized; these statements must not be rendered as assigning it a positive-infinity value.

## Possible future consumer checks

The following recipe identifies the selected types and prospective terminal axiom checks. It has **not** been run as part of this documentation preparation. It creates no new accepted report or importing-consumer result.

```lean
import Obstructions

#check PrimeIdealDivergence.ideal_reciprocals_not_summable
#print axioms PrimeIdealDivergence.ideal_reciprocals_not_summable
#check PrimeIdealDivergence.prime_reciprocals_not_summable
#print axioms PrimeIdealDivergence.prime_reciprocals_not_summable
#check PrimeIdealDivergence.prime_tail_reciprocals_not_summable
#print axioms PrimeIdealDivergence.prime_tail_reciprocals_not_summable
#check PrimeIdealDivergence.prime_tail_reciprocals_unbounded
#print axioms PrimeIdealDivergence.prime_tail_reciprocals_unbounded
```

Historical source acceptance and the separately saved architecture terminal reports are documented in the package's verification material. A future replay would need to preserve their pinned environment and verify the actual output; the recipe itself supplies neither execution authorization nor fresh verification. The selection is a guide to an existing formal interface, without a current-upstream absence or novelty claim.
