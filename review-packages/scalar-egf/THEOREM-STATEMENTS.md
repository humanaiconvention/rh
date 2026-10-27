# Exact scalar EGF derivative statement

The sole public signature is copied verbatim from the unchanged source, with its proof introduction omitted. Context: `module`, four `public import` statements, `noncomputable section`, `public section`, `set_option autoImplicit false`, `open Set Filter` and `open scoped Topology BigOperators`. Complex scalars and functions are explicit. Two private implementation helpers are present but are not public exports.

```lean
theorem HasFPowerSeriesOnBall.iteratedDeriv_ofScalars
    {f : ℂ → ℂ} {c : ℕ → ℂ} {r : ENNReal}
    (h : HasFPowerSeriesOnBall f
      (FormalMultilinearSeries.ofScalars ℂ
        (fun n => c n / (Nat.factorial n : ℂ))) 0 r)
    (k : ℕ) :
    HasFPowerSeriesOnBall (iteratedDeriv k f)
      (FormalMultilinearSeries.ofScalars ℂ
        (fun n => c (n + k) / (Nat.factorial n : ℂ))) 0 r
```

The premise is an existing `HasFPowerSeriesOnBall` representation with coefficients `c n / (Nat.factorial n : ℂ)`, center zero and `r : ENNReal`. Its radius conditions remain part of that premise. For each natural `k`, including zero, the conclusion represents `iteratedDeriv k f` on that **same** center and radius, with coefficients `c (n+k) / n!`, not `c (n+k)/(n+k)!`.

This does not manufacture convergence from a merely assigned pointwise sum, identify a maximal convergence radius, prove a uniform-in-order bound or export an arbitrary-center/target/automatic-entireness theorem. The `egfRow` definition and `egfStep` theorem are private. [Source](IteratedDerivOfScalars.lean), [roster](evidence/public-declarations.json), [verification](VERIFICATION.md).
