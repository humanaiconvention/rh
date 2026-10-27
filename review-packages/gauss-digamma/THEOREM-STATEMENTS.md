# Exact package-owned statements and hypotheses

The headers below are copied literally from the unchanged source, including attribute-prefixed lemmas; proof introductions or definition bodies are omitted. All 39 public lemmas/theorems and six definitions are included. Twenty-three propositions have saved terminal axiom reports; sixteen other compiled propositions are explicitly listed in the [roster](evidence/public-declarations.json), without a separate historical print being implied.

The principal conclusions are `DigammaGauss.digamma_difference_exp` and `DigammaGauss.gauss_integrable_exp`. Their reference `a` is **real** with `0<a`; `z` is complex with `0<z.re`. The integral uses real Lebesgue measure restricted to `Ioi 0`, with complex values. Its numerator is `exp(-a*x) - exp(-z*x)` and the difference is `digamma z - digamma (a:ℂ)`. Genuine integrability is a conclusion, not a premise.

The Gamma-ratio intermediate results permit two complex positive-real-part parameters. That does not extend the exported Gauss integral to complex reference `a`. DCT uses a real parameter approaching zero from above, with a dominator independent of that parameter but dependent on `a,z`. The change of variables `t=exp(-x)` retains the positive absolute Jacobian. Unconditional equalities of totalized Lean integrals do not alone establish convergence; the separate integrability equivalence and final theorem do.

Source contexts are preserved: each helper namespace opens its displayed `Set`, `Filter`, `MeasureTheory` or `Complex` context, and uses `noncomputable section`/`open scoped Topology` as in [DigammaGauss.lean](DigammaGauss.lean). Final definitions refer to `Complex.digamma`, existing Mathlib Gamma/Beta and standard Lebesgue integration. No explicit-formula/RH premise occurs. No assertion at the excluded endpoint zero or separately exported endpoint-limit theorem is added.

## `DigammaGauss.BetaDomination.powerDiff`

[DigammaGauss.lean, line 31](DigammaGauss.lean#L31)

```lean
def powerDiff (a : ℝ) (z : ℂ) (t : ℝ) : ℂ
```

## `DigammaGauss.BetaDomination.betaDifferenceIntegrand`

[DigammaGauss.lean, line 34](DigammaGauss.lean#L34)

```lean
def betaDifferenceIntegrand (a : ℝ) (z : ℂ) (h t : ℝ) : ℂ
```

## `DigammaGauss.BetaDomination.limitKernel`

[DigammaGauss.lean, line 37](DigammaGauss.lean#L37)

```lean
def limitKernel (a : ℝ) (z : ℂ) (t : ℝ) : ℂ
```

## `DigammaGauss.BetaDomination.powerDiff_one`

[DigammaGauss.lean, line 40](DigammaGauss.lean#L40)

```lean
@[simp] lemma powerDiff_one (a : ℝ) (z : ℂ) : powerDiff a z 1=0
```

## `DigammaGauss.BetaDomination.powerDiff_differentiableAt`

[DigammaGauss.lean, line 43](DigammaGauss.lean#L43)

```lean
lemma powerDiff_differentiableAt (a : ℝ) (z : ℂ) {t : ℝ} (ht : 0<t) :
    DifferentiableAt ℝ (powerDiff a z) t
```

## `DigammaGauss.BetaDomination.exists_right_cancel_bound`

[DigammaGauss.lean, line 53](DigammaGauss.lean#L53)

```lean
theorem exists_right_cancel_bound (a : ℝ) (z : ℂ) :
    ∃ C : ℝ, 0<C ∧ ∀ t ∈ Icc (1/2 : ℝ) 1,
      ‖powerDiff a z t‖ ≤ C*(1-t)
```

## `DigammaGauss.BetaDomination.powerDiff_norm_le`

[DigammaGauss.lean, line 80](DigammaGauss.lean#L80)

```lean
lemma powerDiff_norm_le (a : ℝ) (z : ℂ) {t : ℝ} (ht : 0<t) :
    ‖powerDiff a z t‖ ≤ t^(a-1)+t^(z.re-1)
```

## `DigammaGauss.BetaDomination.betaFactor_norm_le`

[DigammaGauss.lean, line 86](DigammaGauss.lean#L86)

```lean
lemma betaFactor_norm_le {h t : ℝ} (hh : 0≤h) (ht : t∈Ioo (0 : ℝ) 1) :
    ‖(1-(t : ℂ))^((h : ℂ)-1)‖ ≤ (1-t)⁻¹
```

## `DigammaGauss.BetaDomination.dominator`

[DigammaGauss.lean, line 97](DigammaGauss.lean#L97)

```lean
def dominator (a : ℝ) (z : ℂ) (C t : ℝ) : ℝ
```

## `DigammaGauss.BetaDomination.dominated`

[DigammaGauss.lean, line 100](DigammaGauss.lean#L100)

```lean
lemma dominated {a : ℝ} {z : ℂ} {C : ℝ}
    (hC : ∀ t∈Icc (1/2 : ℝ) 1, ‖powerDiff a z t‖≤C*(1-t))
    {h t : ℝ} (hh : 0≤h) (ht : t∈Ioo (0 : ℝ) 1) :
    ‖betaDifferenceIntegrand a z h t‖≤dominator a z C t
```

## `DigammaGauss.BetaDomination.dominator_integrable`

[DigammaGauss.lean, line 122](DigammaGauss.lean#L122)

```lean
lemma dominator_integrable {a : ℝ} {z : ℂ} (ha : 0<a) (hz : 0<z.re) (C : ℝ) :
    IntegrableOn (dominator a z C) (Ioo (0 : ℝ) 1)
```

## `DigammaGauss.BetaLimit.integrand_continuousOn`

[DigammaGauss.lean, line 149](DigammaGauss.lean#L149)

```lean
lemma integrand_continuousOn (a : ℝ) (z : ℂ) (h : ℝ) :
    ContinuousOn (betaDifferenceIntegrand a z h) (Ioo (0 : ℝ) 1)
```

## `DigammaGauss.BetaLimit.integrand_zero`

[DigammaGauss.lean, line 161](DigammaGauss.lean#L161)

```lean
lemma integrand_zero (a : ℝ) (z : ℂ) (t : ℝ) :
    betaDifferenceIntegrand a z 0 t=limitKernel a z t
```

## `DigammaGauss.BetaLimit.integrand_tendsto`

[DigammaGauss.lean, line 165](DigammaGauss.lean#L165)

```lean
lemma integrand_tendsto (a : ℝ) (z : ℂ) (t : ℝ) :
    Tendsto (fun h : ℝ => betaDifferenceIntegrand a z h t) (𝓝[>] 0) (𝓝 (limitKernel a z t))
```

## `DigammaGauss.BetaLimit.limitKernel_integrable`

[DigammaGauss.lean, line 175](DigammaGauss.lean#L175)

```lean
theorem limitKernel_integrable {a : ℝ} {z : ℂ} (ha : 0<a) (hz : 0<z.re) :
    IntegrableOn (limitKernel a z) (Ioo (0 : ℝ) 1)
```

## `DigammaGauss.BetaLimit.cancelled_integral_limit`

[DigammaGauss.lean, line 188](DigammaGauss.lean#L188)

```lean
theorem cancelled_integral_limit {a : ℝ} {z : ℂ} (ha : 0<a) (hz : 0<z.re) :
    Tendsto (fun h : ℝ => ∫ t in Ioo (0 : ℝ) 1, betaDifferenceIntegrand a z h t)
      (𝓝[>] 0) (𝓝 (∫ t in Ioo (0 : ℝ) 1, limitKernel a z t))
```

## `DigammaGauss.BetaLimit.beta_difference_eq_integral`

[DigammaGauss.lean, line 200](DigammaGauss.lean#L200)

```lean
lemma beta_difference_eq_integral {a : ℝ} {z : ℂ} (ha : 0<a) (hz : 0<z.re)
    {h : ℝ} (hh : 0<h) :
    Complex.betaIntegral (a : ℂ) (h : ℂ)-Complex.betaIntegral z (h : ℂ)=
      ∫ t in Ioo (0 : ℝ) 1, betaDifferenceIntegrand a z h t
```

## `DigammaGauss.BetaLimit.beta_difference_integral_limit`

[DigammaGauss.lean, line 218](DigammaGauss.lean#L218)

```lean
theorem beta_difference_integral_limit {a : ℝ} {z : ℂ} (ha : 0<a) (hz : 0<z.re) :
    Tendsto (fun h : ℝ => Complex.betaIntegral (a : ℂ) (h : ℂ)-Complex.betaIntegral z (h : ℂ))
      (𝓝[>] 0) (𝓝 (∫ t in Ioo (0 : ℝ) 1, limitKernel a z t))
```

## `DigammaGauss.Substitution.image_exp_neg`

[DigammaGauss.lean, line 242](DigammaGauss.lean#L242)

```lean
lemma image_exp_neg : (fun x : ℝ => Real.exp (-x)) '' Ioi (0 : ℝ)=Ioo (0 : ℝ) 1
```

## `DigammaGauss.Substitution.exp_neg_deriv`

[DigammaGauss.lean, line 253](DigammaGauss.lean#L253)

```lean
lemma exp_neg_deriv (x : ℝ) :
    HasDerivAt (fun y : ℝ => Real.exp (-y)) (-Real.exp (-x)) x
```

## `DigammaGauss.Substitution.exp_neg_injective`

[DigammaGauss.lean, line 257](DigammaGauss.lean#L257)

```lean
lemma exp_neg_injective : Function.Injective (fun x : ℝ => Real.exp (-x))
```

## `DigammaGauss.Substitution.integral_exp_neg`

[DigammaGauss.lean, line 262](DigammaGauss.lean#L262)

```lean
theorem integral_exp_neg (G : ℝ → ℂ) :
    (∫ t in Ioo (0 : ℝ) 1, G t)=
      ∫ x in Ioi (0 : ℝ), Real.exp (-x) • G (Real.exp (-x))
```

## `DigammaGauss.Substitution.integrable_exp_neg`

[DigammaGauss.lean, line 271](DigammaGauss.lean#L271)

```lean
theorem integrable_exp_neg (G : ℝ → ℂ) :
    IntegrableOn G (Ioo (0 : ℝ) 1) ↔
      IntegrableOn (fun x : ℝ => Real.exp (-x) • G (Real.exp (-x))) (Ioi (0 : ℝ))
```

## `DigammaGauss.Substitution.exp_neg_cpow`

[DigammaGauss.lean, line 279](DigammaGauss.lean#L279)

```lean
lemma exp_neg_cpow (x : ℝ) (w : ℂ) :
    (Real.exp (-x) : ℂ)^w=Complex.exp (-(x : ℂ)*w)
```

## `DigammaGauss.Substitution.jacobian_power`

[DigammaGauss.lean, line 285](DigammaGauss.lean#L285)

```lean
lemma jacobian_power (x : ℝ) (w : ℂ) :
    (Real.exp (-x) : ℂ)*(Real.exp (-x) : ℂ)^(w-1)=
      Complex.exp (-w*(x : ℂ))
```

## `DigammaGauss.Substitution.gaussKernel`

[DigammaGauss.lean, line 293](DigammaGauss.lean#L293)

```lean
def gaussKernel (a : ℝ) (z : ℂ) (x : ℝ) : ℂ
```

## `DigammaGauss.Substitution.jacobian_kernel`

[DigammaGauss.lean, line 298](DigammaGauss.lean#L298)

```lean
lemma jacobian_kernel (a : ℝ) (z : ℂ) (x : ℝ) :
    Real.exp (-x) • limitKernel a z (Real.exp (-x))=gaussKernel a z x
```

## `DigammaGauss.Substitution.limitKernel_integral`

[DigammaGauss.lean, line 305](DigammaGauss.lean#L305)

```lean
theorem limitKernel_integral (a : ℝ) (z : ℂ) :
    (∫ t in Ioo (0 : ℝ) 1, limitKernel a z t)=
      ∫ x in Ioi (0 : ℝ), gaussKernel a z x
```

## `DigammaGauss.GammaRatio.ratioDifference`

[DigammaGauss.lean, line 330](DigammaGauss.lean#L330)

```lean
def ratioDifference (a z h : ℂ) : ℂ
```

## `DigammaGauss.GammaRatio.positive_not_pole`

[DigammaGauss.lean, line 333](DigammaGauss.lean#L333)

```lean
lemma positive_not_pole {a : ℂ} (ha : 0<a.re) : ∀m:ℕ,a≠-(m:ℂ)
```

## `DigammaGauss.GammaRatio.gamma_ratio_zero`

[DigammaGauss.lean, line 340](DigammaGauss.lean#L340)

```lean
lemma gamma_ratio_zero {a : ℂ} (ha : 0<a.re) : Gamma a/Gamma (a+0)=1
```

## `DigammaGauss.GammaRatio.gamma_ratio_hasDerivAt`

[DigammaGauss.lean, line 343](DigammaGauss.lean#L343)

```lean
lemma gamma_ratio_hasDerivAt {a : ℂ} (ha : 0<a.re) :
    HasDerivAt (fun h:ℂ=>Gamma a/Gamma (a+h)) (-digamma a) 0
```

## `DigammaGauss.GammaRatio.ratioDifference_zero`

[DigammaGauss.lean, line 358](DigammaGauss.lean#L358)

```lean
@[simp] lemma ratioDifference_zero {a z : ℂ} (ha : 0<a.re) (hz : 0<z.re) :
    ratioDifference a z 0=0
```

## `DigammaGauss.GammaRatio.ratioDifference_hasDerivAt`

[DigammaGauss.lean, line 362](DigammaGauss.lean#L362)

```lean
lemma ratioDifference_hasDerivAt {a z : ℂ} (ha : 0<a.re) (hz : 0<z.re) :
    HasDerivAt (ratioDifference a z) (digamma z-digamma a) 0
```

## `DigammaGauss.GammaRatio.ratioDifference_slope_limit`

[DigammaGauss.lean, line 368](DigammaGauss.lean#L368)

```lean
lemma ratioDifference_slope_limit {a z : ℂ} (ha : 0<a.re) (hz : 0<z.re) :
    Tendsto (fun h:ℝ=>ratioDifference a z (h:ℂ)/(h:ℂ)) (𝓝[>] 0)
      (𝓝 (digamma z-digamma a))
```

## `DigammaGauss.GammaRatio.ofReal_tendsto_zero_right_ne`

[DigammaGauss.lean, line 383](DigammaGauss.lean#L383)

```lean
lemma ofReal_tendsto_zero_right_ne :
    Tendsto (fun h:ℝ=>(h:ℂ)) (𝓝[>] 0) (𝓝[≠] (0:ℂ))
```

## `DigammaGauss.GammaRatio.gamma_times_ratio_limit`

[DigammaGauss.lean, line 392](DigammaGauss.lean#L392)

```lean
lemma gamma_times_ratio_limit {a z : ℂ} (ha : 0<a.re) (hz : 0<z.re) :
    Tendsto (fun h:ℝ=>Gamma (h:ℂ)*ratioDifference a z (h:ℂ)) (𝓝[>] 0)
      (𝓝 (digamma z-digamma a))
```

## `DigammaGauss.GammaRatio.beta_difference_identity`

[DigammaGauss.lean, line 405](DigammaGauss.lean#L405)

```lean
lemma beta_difference_identity {a z : ℂ} (ha : 0<a.re) (hz : 0<z.re)
    {h : ℝ} (hh : 0<h) :
    betaIntegral a (h:ℂ)-betaIntegral z (h:ℂ)=
      Gamma (h:ℂ)*ratioDifference a z (h:ℂ)
```

## `DigammaGauss.GammaRatio.beta_difference_limit_complex`

[DigammaGauss.lean, line 427](DigammaGauss.lean#L427)

```lean
theorem beta_difference_limit_complex {a z : ℂ} (ha : 0<a.re) (hz : 0<z.re) :
    Tendsto (fun h:ℝ=>betaIntegral a (h:ℂ)-betaIntegral z (h:ℂ)) (𝓝[>] 0)
      (𝓝 (digamma z-digamma a))
```

## `DigammaGauss.GammaRatio.beta_difference_limit`

[DigammaGauss.lean, line 434](DigammaGauss.lean#L434)

```lean
theorem beta_difference_limit {a : ℝ} {z : ℂ} (ha : 0<a) (hz : 0<z.re) :
    Tendsto (fun h:ℝ=>betaIntegral (a:ℂ) (h:ℂ)-betaIntegral z (h:ℂ)) (𝓝[>] 0)
      (𝓝 (digamma z-digamma (a:ℂ)))
```

## `DigammaGauss.beta_domain_digamma`

[DigammaGauss.lean, line 461](DigammaGauss.lean#L461)

```lean
theorem beta_domain_digamma {a : ℝ} {z : ℂ} (ha : 0<a) (hz : 0<z.re) :
    Complex.digamma z-Complex.digamma (a : ℂ)=
      ∫ t in Ioo (0 : ℝ) 1, limitKernel a z t
```

## `DigammaGauss.gauss_integrable`

[DigammaGauss.lean, line 468](DigammaGauss.lean#L468)

```lean
theorem gauss_integrable {a : ℝ} {z : ℂ} (ha : 0<a) (hz : 0<z.re) :
    IntegrableOn (gaussKernel a z) (Ioi (0 : ℝ))
```

## `DigammaGauss.digamma_difference`

[DigammaGauss.lean, line 475](DigammaGauss.lean#L475)

```lean
theorem digamma_difference {a : ℝ} {z : ℂ} (ha : 0<a) (hz : 0<z.re) :
    Complex.digamma z-Complex.digamma (a : ℂ)=
      ∫ x in Ioi (0 : ℝ), gaussKernel a z x
```

## `DigammaGauss.digamma_difference_exp`

[DigammaGauss.lean, line 481](DigammaGauss.lean#L481)

```lean
theorem digamma_difference_exp {a : ℝ} {z : ℂ} (ha : 0<a) (hz : 0<z.re) :
    Complex.digamma z-Complex.digamma (a : ℂ)=
      ∫ x in Ioi (0 : ℝ),
        ((Real.exp (-a*x) : ℂ)-Complex.exp (-z*(x : ℂ)))/(1-(Real.exp (-x) : ℂ))
```

## `DigammaGauss.gauss_integrable_exp`

[DigammaGauss.lean, line 495](DigammaGauss.lean#L495)

```lean
theorem gauss_integrable_exp {a : ℝ} {z : ℂ} (ha : 0<a) (hz : 0<z.re) :
    IntegrableOn (fun x : ℝ =>
      ((Real.exp (-a*x) : ℂ)-Complex.exp (-z*(x : ℂ)))/(1-(Real.exp (-x) : ℂ)))
      (Ioi (0 : ℝ))
```
