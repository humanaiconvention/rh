# Gauss U03 — Lean 4.37.0-rc1 review candidate

**Lean 4.37.0-rc1 candidate: BUILD NOT RUN.**
**Lean 4.36.0-rc2: historical three-source direct-Lean replay only.**
**Strict independent replay and human review: PENDING. Not submission-ready.**

Candidate ID: `U03-lean437rc1-linked-public-provider-review-001`.

This formalizes a **classical Gauss digamma identity**, including actual integrability as a separate result. It is not a new analytic result, an RH claim or a tested new Lean edition. The one configuration-layout change below is unbuilt.

## Read these first

1. [GaussDigamma.lean](GaussDigamma.lean): the two exact public contracts.
2. [PackageConsumer.lean](PackageConsumer.lean): independent typed uses of both contracts.
3. The [existing public provider, pinned to its prior commit](https://github.com/humanaiconvention/rh/blob/475a9d9639f347bb1b72ae30a129d5d330275454/review-packages/gauss-digamma/DigammaGauss.lean). It is unchanged and already present in this branch's public base; it is not copied into this new edition.
4. [Evidence and reproduction](REPRODUCE.md), [source/rights boundary](PROVENANCE-AND-HOLDBACKS.md), [candidate manifest](CANDIDATE.json).

The proof stays in `review-packages/gauss-digamma/DigammaGauss.lean`. This edition's `DigammaGauss` library has one added `srcDir` line pointing there. API, consumer, toolchain, nine-entry lock and independent Challenge retain their frozen bytes. [Original TOML](baseline/lakefile.toml) and [the exact layout diff](LAYOUT.diff) preserve the change. No historical package file or seal was edited.

## Two exact claims

For real `a > 0` and complex `z` with `0 < z.re`, the public declarations are:

```lean
theorem difference_integral {a : ℝ} {z : ℂ} (ha : 0 < a) (hz : 0 < z.re) :
    Complex.digamma z - Complex.digamma (a : ℂ) =
      ∫ x in Ioi (0 : ℝ),
        ((Real.exp (-a * x) : ℂ) - Complex.exp (-z * (x : ℂ))) /
          (1 - (Real.exp (-x) : ℂ))

theorem integrable_difference {a : ℝ} {z : ℂ} (ha : 0 < a) (hz : 0 < z.re) :
    IntegrableOn (fun x : ℝ =>
      ((Real.exp (-a * x) : ℂ) - Complex.exp (-z * (x : ℂ))) /
        (1 - (Real.exp (-x) : ℂ))) (Ioi (0 : ℝ))
```

They are in namespace `GaussDigamma`, with `Set` and `MeasureTheory` open. The integral is complex-valued with Lebesgue measure on the open positive half-line. Integrability is a conclusion, not a premise. Neither a wider domain nor an RH hypothesis is claimed.

The proof subtracts Beta integrals before taking the second parameter to zero, obtains an integrable cancellation bound, identifies the Gamma-ratio derivative and substitutes `t = exp(-x)`. See the prior public provider and [its existing explanation](https://github.com/humanaiconvention/rh/blob/475a9d9639f347bb1b72ae30a129d5d330275454/review-packages/gauss-digamma/README.md).

## Exact pins and evidence

- Lean `v4.37.0-rc1`, source commit `0b77e12952ad39077d80d8bd6b66d601f225c321`.
- Mathlib `31ce06eaadf4a200c0e1407c5f10953cf606b8f8`; all nine exact Git revisions remain in the unchanged [lock](lake-manifest.json) and [pin table](PINS.md). No floating update was run.
- Current clean Lake build, consumer, expanded Challenge/type comparison and axiom audit: **NOT RUN**. The prepared lock is not a newly Lake-validated resolution.
- [Historical rc2 receipt](evidence/historical-rc2-replay.json): same three proof-source hashes, Lean 4.36.0-rc2 / Mathlib `9d581dfff2e41de989072ea63abf3daf69311520`, 27 named reports using only `propext`, `Classical.choice`, `Quot.sound`. This was serial local direct-Lean replay with authenticated upstream cached artifacts; not a new rc1 build or strict source rebuild.
- [Sanitized 3158–3159 receipt](evidence/maintenance-3158-3159.json): missing staged Mathlib config, then fetch stopped at an unadmitted Git dispatcher. No usable checkout, network verdict or Lean result followed.
- [Challenge](challenge/README.md): frozen Mathlib-only specification, outside the default build. Its two intentional holes are not solution or verification evidence.

No already-qualified runner with the exact accepted inputs was available for this pass. No build-runner development, dependency fetch retry, widened allowance, Lean job, strict comparator or wrong-statement control ran. Human mathematical, provenance and rights review remain pending. The existing provider's historical rights limit is disclosed, not cleared by its prior public availability.

Preparation is AI-assisted under human direction. No external review, upstream PR, release tag or submission is asserted. This packaging commit uses `[skip ci]` so its push does not trigger the old certificate workflow; skipped CI supplies no verification evidence.
