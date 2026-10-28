# Prime-ideal harmonic divergence in every number field

The existing [Obstructions.lean](Obstructions.lean) contains a reusable theorem
that does not depend on its later architecture parameters. For every number
field K, the reciprocals of the absolute norms of its nonzero prime ideals form
a nonsummable family of real numbers:

$$
\neg\operatorname{Summable}\left(\mathfrak p\longmapsto
\frac{1}{N\mathfrak p}\right).
$$

The theorem is `PrimeIdealDivergence.prime_reciprocals_not_summable`.
Its explicit typeclass assumptions are `[Field K] [NumberField K]`.
`normI` is the real cast of `Ideal.absNorm`; `PrimeIdeal K` uses Lean's
multiplicative prime predicate on ideals, which excludes zero and units.
The factorization below is factorization of **ideals**, not of elements.
There is no class-number-one or element unique-factorization hypothesis.

For any finite excluded set S, the same source proves the concrete tail form:

$$
\forall B\in\mathbb R,\quad \exists F\text{ finite},\quad
F\subseteq\{\mathfrak p\mid\mathfrak p\notin S,\;64\leq N\mathfrak p\},
\qquad B<\sum_{\mathfrak p\in F}\frac1{N\mathfrak p}.
$$

The cutoff 64 is retained exactly as exported. This is an unordered finite-subsum
statement; no enumeration of prime ideals is chosen. It supplies no quantitative
growth rate or separately exported norm-ordered partial-sum limit. In particular,
the result is not a claim that Lean's totalized real `tsum` takes the value
positive infinity. Read the [selected exact API](PrimeIdealDivergenceAPI.md).

## Why the proof works

First consider **all nonzero ideals**. Mathlib supplies finiteness of bounded
absolute-norm sets and the ideal-count asymptotic

$$
\frac{\#\{I\ne0:NI\leq x\}}{x}\longrightarrow c_K,\qquad c_K\ne0,
$$

with c_K identified with the Dedekind-zeta residue. The proof uses the nonzero
residue theorem, not an assumed prime-distribution or zero-location statement.

If ideal reciprocals were summable, the functions

$$
f_x(I)=\begin{cases}1/x&NI\leq x,\\0&NI>x\end{cases}
$$

would tend pointwise to zero and, eventually, be dominated by the summable
family 1/NI. Dominated convergence for sums would force their sum, the displayed
ideal-count quotient, to tend to zero. Uniqueness of the limit contradicts
c_K ≠ 0. This proves `ideal_reciprocals_not_summable`.

Next suppose prime-ideal reciprocals were summable. Define rho(I)=1/NI on prime
ideals and zero otherwise. The source proves 0 ≤ rho(I) ≤ 1/2, so

$$
\sum_{n\geq0}\rho(I)^{n+1}=\frac{\rho(I)}{1-\rho(I)}
\leq2\rho(I).
$$

Thus the positive prime-power family is summable. Mathlib's finite-product
summability result then makes the family of products over finite sets of
ideal/exponent pairs summable. Every nonzero ideal has an exact factorization
tag in that family. `tags_prod` reconstructs the ideal, `tags_injective` proves
different ideals have different tags, and `tags_weight` identifies the product
weight with 1/NI. Pulling back along this injection would make all ideal
reciprocals summable, contradicting the first step.

Finally, a finite excluded set and the prime ideals of norm below 64 contribute
only a finite family. Removing them preserves nonsummability. Positivity turns
that conclusion into the stated unbounded finite-subsum theorem.

## The reusable boundary

The generic proof uses established Mathlib ideal counting, Dedekind-zeta residue,
ideal factorization, absolute-norm and summability infrastructure. Its source
imports umbrella `Mathlib`; this guide does not claim a minimal import graph.
It documents a classical result and its existing formal interface, without a
mathematical-priority or current-upstream absence claim.

The later `RHArchitectureObstructions` namespace specializes the tail theorem
to its Eisenstein field, then combines it with the specified local Euler-factor
comparison. That specialization has additional parameters and hypotheses;
the generic theorem does not inherit them. Conversely, the generic divergence
does not turn a fixed-factor absolute-convergence obstruction into a general
analytic impossibility result. The [package overview](README.md) retains the
application's exact exponent, moment and strip restrictions.

## What the verification evidence establishes

The accepted original source has SHA-256
`f8255264e049f39706786d6b549db81b2fb20c5d58ba9200c29003b7deef63ac`.
The already-public source has SHA-256
`314ca529810b8b517592e1b502711b5abf65c32e2bbe928b8298def3f07e9046`.
They are different files: public packaging changed comments and added the
module/export wrapper. The entire `PrimeIdealDivergence` namespace was checked
to be literally identical. A separate existing public-wrapper verification
record matches the public source hash and the same Lean 4.35.0 / Mathlib
`6015dbbfc399f4548bafd46f9560ff61595fd328` pins. The original receipt alone
is not used as acceptance of the different wrapper.

Both are historical whole-module results. The seven directly printed axiom
reports concern architecture declarations; the generic helper has no separate
saved terminal report. The downstream Eisenstein and unconditional Euler
declarations reach its proof, with only `propext`, `Classical.choice`, and
`Quot.sound` in their recorded transitive audits. The public log repeats those
seven declarations once during the build and once during the direct compiler
check; fourteen occurrences are not fourteen different theorem audits.

[PRIME-IDEAL-EVIDENCE.json](PRIME-IDEAL-EVIDENCE.json) maps the exact statements,
source identities, original/public receipts and downstream reachability.
No source, import, toolchain or dependency was changed for this guide. No fresh
compiler, importer, minimal-import extraction or version-port check ran.
The existing [provenance record](provenance/README.md), notices and historical
reports remain in place. This explanatory preparation was AI-assisted; exact
historical model identities are not authenticated, and internal review is not
external independent review.
