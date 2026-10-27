# Exact actual-density statements and complete supporting API

All317 package-owned public declarations follow literally:248 declared theorem,10 declared lemma and59 definitions. There are no private/protected declarations or global variable blocks in this selected source closure. The original source opens/noncomputable sections remain in each linked file;all headings use actual full namespace names,not module-label abbreviations. The anonymous section inside `ThetaShellShape` does not change namespace ownership. The two sequential namespaces in `MonotoneMomentOrder` are distinguished.

The three main actual-density conclusions are `ThetaMacdonald.Crossing.actual_density_crossing`, `ThetaMacdonald.Cumulative.actual_CDF_strict_order` and `ThetaMacdonald.Moment.actual_power_moment_order`. None assumes its desired order or RH. The crossing is unique on the nonnegative half-line:theta is below Macdonald for0≤u<c and above foru>c. For every real u>0,the theta cumulative integral is smaller. For each natural n>0,the Macdonald power moment is smaller. Weighted integrability is proved;zeroth moments are equal. No arbitrary real-power or uniform-in-exponent assertion is exported.

The general `actual_monotone_weight_order` requires both genuine weighted `IntegrableOn` premises,`MonotoneOn` on `Ioi 0`,and the full condition `∀ c>0,∃ b>c,w c<w b`. The generic SingleCrossing and exponential-bound helpers retain their displayed hypotheses;their compilation is not confused with the fully instantiated actual-density roots.

[Actual definitions and normalization](SOURCE-DEFINITIONS.md) retain the complete infinite Phi series,zero shell,the real positive gamma0,its exact complex standard-zeta xiHalf identification,original Macdonald K0 integral,factor2 and argument2u. Set integrals use actual Lebesgue measure on the shown domains;the CDF theorem uses the interval integral0..u. The normalizers are proved,not free parameters. The preserved Mellin bridge's assigned theta endpoint and a.e./positive-half-line argument are not silently replaced by a pointwise endpoint identity.

One hundred fifty-seven declarations have actual saved terminal axiom reports. The other101compiled public propositions are named explicitly in the [roster](evidence/public-declarations.json);no separate historical print is invented. [Local dependency closure](DEPENDENCY-HANDOFF.md), [verification](VERIFICATION.md).

## `SingleCrossing.integrable_tail`

[CumulativeSplit.lean,line 11](CumulativeSplit.lean#L11)

```lean
theorem integrable_tail {f : ℝ → ℝ}
    (hf : IntegrableOn f (Ioi (0 : ℝ))) {u : ℝ} (hu : 0 ≤ u) :
    IntegrableOn f (Ioi u)
```

## `SingleCrossing.intervalIntegrable_head`

[CumulativeSplit.lean,line 16](CumulativeSplit.lean#L16)

```lean
theorem intervalIntegrable_head {f : ℝ → ℝ}
    (hf : IntegrableOn f (Ioi (0 : ℝ))) {u : ℝ} (hu : 0 ≤ u) :
    IntervalIntegrable f volume 0 u
```

## `SingleCrossing.head_tail_split`

[CumulativeSplit.lean,line 22](CumulativeSplit.lean#L22)

```lean
theorem head_tail_split {f : ℝ → ℝ}
    (hf : IntegrableOn f (Ioi (0 : ℝ))) {u : ℝ} (hu : 0 ≤ u) :
    (∫ t in (0 : ℝ)..u, f t)+(∫ t in Ioi u, f t) =
      ∫ t in Ioi (0 : ℝ), f t
```

## `SingleCrossing.head_eq_Ioc`

[CumulativeSplit.lean,line 28](CumulativeSplit.lean#L28)

```lean
theorem head_eq_Ioc {f : ℝ → ℝ} {u : ℝ} (hu : 0 ≤ u) :
    (∫ t in (0 : ℝ)..u, f t) = ∫ t in Ioc (0 : ℝ) u, f t
```

## `SingleCrossing.head_eq_Ioo`

[CumulativeSplit.lean,line 32](CumulativeSplit.lean#L32)

```lean
theorem head_eq_Ioo {f : ℝ → ℝ} {u : ℝ} (hu : 0 ≤ u) :
    (∫ t in (0 : ℝ)..u, f t) = ∫ t in Ioo (0 : ℝ) u, f t
```

## `SingleCrossing.head_eq_Icc`

[CumulativeSplit.lean,line 36](CumulativeSplit.lean#L36)

```lean
theorem head_eq_Icc {f : ℝ → ℝ} {u : ℝ} (hu : 0 ≤ u) :
    (∫ t in (0 : ℝ)..u, f t) = ∫ t in Icc (0 : ℝ) u, f t
```

## `SingleCrossing.integral_tail_pos`

[CumulativeSplit.lean,line 40](CumulativeSplit.lean#L40)

```lean
theorem integral_tail_pos {f : ℝ → ℝ} {u : ℝ}
    (hf : IntegrableOn f (Ioi u)) (hp : ∀ t : ℝ, u < t → 0 < f t) :
    0 < ∫ t in Ioi u, f t
```

## `SingleCrossing.strict_prefix_of_single_crossing`

[CumulativeSplit.lean,line 56](CumulativeSplit.lean#L56)

```lean
theorem strict_prefix_of_single_crossing {f : ℝ → ℝ} {c : ℝ}
    (hf : IntegrableOn f (Ioi (0 : ℝ)))
    (hzero : (∫ t in Ioi (0 : ℝ), f t) = 0)
    (hneg : ∀ t : ℝ, 0 < t → t < c → f t < 0)
    (hpos : ∀ t : ℝ, c < t → 0 < f t)
    {u : ℝ} (hu : 0 < u) :
    (∫ t in (0 : ℝ)..u, f t) < 0
```

## `ExponentialMoment.quadratic_exp_integrable`

[ExponentialMomentBounds.lean,line 10](ExponentialMomentBounds.lean#L10)

```lean
theorem quadratic_exp_integrable :
    IntegrableOn (fun t : ℝ => t^2*Real.exp (-t)) (Ioi (0 : ℝ))
```

## `ExponentialMoment.weighted_integrable`

[ExponentialMomentBounds.lean,line 16](ExponentialMomentBounds.lean#L16)

```lean
theorem weighted_integrable {f : ℝ → ℝ} {A : ℝ}
    (hf : IntegrableOn f (Ioi (0 : ℝ)))
    (hb : ∀ t : ℝ, 0 ≤ t → ‖f t‖ ≤ A*Real.exp (-t)) :
    IntegrableOn (fun t : ℝ => t^2*f t) (Ioi (0 : ℝ))
```

## `ExponentialMoment.tail_bound`

[ExponentialMomentBounds.lean,line 32](ExponentialMomentBounds.lean#L32)

```lean
theorem tail_bound {f : ℝ → ℝ} {A : ℝ}
    (hb : ∀ t : ℝ, 0 ≤ t → ‖f t‖ ≤ A*Real.exp (-t))
    {u : ℝ} (hu : 0 ≤ u) :
    ‖∫ t in Ioi u, f t‖ ≤ A*Real.exp (-u)
```

## `ExponentialMoment.quadratic_exp_half_bound`

[ExponentialMomentBounds.lean,line 44](ExponentialMomentBounds.lean#L44)

```lean
theorem quadratic_exp_half_bound (t : ℝ) (ht : 0 ≤ t) :
    t^2*Real.exp (-t) ≤ 8*Real.exp (-t/2)
```

## `ExponentialMoment.weighted_tail_bound`

[ExponentialMomentBounds.lean,line 54](ExponentialMomentBounds.lean#L54)

```lean
theorem weighted_tail_bound {f : ℝ → ℝ} {A : ℝ} (hA : 0 ≤ A)
    (hb : ∀ t : ℝ, 0 ≤ t → ‖f t‖ ≤ A*Real.exp (-t))
    {u : ℝ} (hu : 0 ≤ u) :
    ‖∫ t in Ioi u, t^2*f t‖ ≤ 16*A*Real.exp (-u/2)
```

## `ExponentialMoment.quadratic_boundary_vanishes`

[ExponentialMomentBounds.lean,line 76](ExponentialMomentBounds.lean#L76)

```lean
theorem quadratic_boundary_vanishes {g : ℝ → ℝ} {A : ℝ}
    (hb : ∀ u : ℝ, 0 ≤ u → ‖g u‖ ≤ A*Real.exp (-u)) :
    Tendsto (fun u : ℝ => u^2*g u) atTop (𝓝 0)
```

## `ThetaMacdonald.Density.macdonaldKernel`

[MacdonaldMass.lean,line 14](MacdonaldMass.lean#L14)

```lean
def macdonaldKernel (x t : ℝ) : ℝ
```

## `ThetaMacdonald.Density.macdonaldK0`

[MacdonaldMass.lean,line 15](MacdonaldMass.lean#L15)

```lean
def macdonaldK0 (x : ℝ) : ℝ
```

## `ThetaMacdonald.Density.macdonaldDensity`

[MacdonaldMass.lean,line 16](MacdonaldMass.lean#L16)

```lean
def macdonaldDensity (u : ℝ) : ℝ
```

## `ThetaMacdonald.Density.cosh_lower_half`

[MacdonaldMass.lean,line 19](MacdonaldMass.lean#L19)

```lean
theorem cosh_lower_half {t : ℝ} (ht : 0 ≤ t) :
    t/2 ≤ Real.cosh t
```

## `ThetaMacdonald.Density.integrable_macdonaldKernel`

[MacdonaldMass.lean,line 26](MacdonaldMass.lean#L26)

```lean
theorem integrable_macdonaldKernel {x : ℝ} (hx : 0 < x) :
    IntegrableOn (macdonaldKernel x) (Ioi (0 : ℝ))
```

## `ThetaMacdonald.Density.macdonaldK0_pos`

[MacdonaldMass.lean,line 40](MacdonaldMass.lean#L40)

```lean
theorem macdonaldK0_pos {x : ℝ} (hx : 0 < x) :
    0 < macdonaldK0 x
```

## `ThetaMacdonald.Density.integrable_macdonaldDensity`

[MacdonaldMass.lean,line 52](MacdonaldMass.lean#L52)

```lean
theorem integrable_macdonaldDensity :
    IntegrableOn macdonaldDensity (Ioi (0 : ℝ))
```

## `ThetaMacdonald.Density.macdonaldDensity_pos`

[MacdonaldMass.lean,line 62](MacdonaldMass.lean#L62)

```lean
theorem macdonaldDensity_pos (u : ℝ) : 0 < macdonaldDensity u
```

## `ThetaMacdonald.Density.macdonaldDensity_mass`

[MacdonaldMass.lean,line 66](MacdonaldMass.lean#L66)

```lean
theorem macdonaldDensity_mass :
    (∫ u in Ioi (0 : ℝ), macdonaldDensity u) = 1
```

## `ThetaMacdonald.Density.macdonaldDensity_mass_closed`

[MacdonaldMass.lean,line 81](MacdonaldMass.lean#L81)

```lean
theorem macdonaldDensity_mass_closed :
    (∫ u in Ici (0 : ℝ), macdonaldDensity u) = 1
```

## `SingleCrossing.strict_integral_order_of_monotone_weight`

[MonotoneMomentOrder.lean,line 9](MonotoneMomentOrder.lean#L9)

```lean
theorem strict_integral_order_of_monotone_weight
    {f g w : ℝ → ℝ} {c : ℝ}
    (hf : IntegrableOn f (Ioi (0 : ℝ)))
    (hg : IntegrableOn g (Ioi (0 : ℝ)))
    (hwf : IntegrableOn (fun u => w u*f u) (Ioi (0 : ℝ)))
    (hwg : IntegrableOn (fun u => w u*g u) (Ioi (0 : ℝ)))
    (hmass : (∫ u in Ioi (0 : ℝ), f u) = ∫ u in Ioi (0 : ℝ), g u)
    (hc : 0 < c)
    (hleft : ∀ u : ℝ, 0 < u → u < c → f u < g u)
    (hright : ∀ u : ℝ, c < u → g u < f u)
    (hw : MonotoneOn w (Ioi (0 : ℝ)))
    (hstrict : ∃ b : ℝ, c < b ∧ w c < w b) :
    (∫ u in Ioi (0 : ℝ), w u*g u) <
      ∫ u in Ioi (0 : ℝ), w u*f u
```

## `ExponentialMoment.power_exp_integrable`

[MonotoneMomentOrder.lean,line 77](MonotoneMomentOrder.lean#L77)

```lean
theorem power_exp_integrable (n : ℕ) :
    IntegrableOn (fun t : ℝ => t^n*Real.exp (-t)) (Ioi (0 : ℝ))
```

## `ExponentialMoment.power_weighted_integrable`

[MonotoneMomentOrder.lean,line 83](MonotoneMomentOrder.lean#L83)

```lean
theorem power_weighted_integrable {f : ℝ → ℝ} {A : ℝ} (n : ℕ)
    (hf : IntegrableOn f (Ioi (0 : ℝ)))
    (hb : ∀ t : ℝ, 0 ≤ t → ‖f t‖ ≤ A*Real.exp (-t)) :
    IntegrableOn (fun t : ℝ => t^n*f t) (Ioi (0 : ℝ))
```

## `RhWeilCompletedGrowth.gaussianMass`

[RhWeilCompletedGrowth001.lean,line 14](RhWeilCompletedGrowth001.lean#L14)

```lean
def gaussianMass (p : ℝ) : ℝ
```

## `RhWeilCompletedGrowth.gaussianMass_nonneg`

[RhWeilCompletedGrowth001.lean,line 16](RhWeilCompletedGrowth001.lean#L16)

```lean
lemma gaussianMass_nonneg (p : ℝ) : 0≤gaussianMass p
```

## `RhWeilCompletedGrowth.weighted_integrable`

[RhWeilCompletedGrowth001.lean,line 19](RhWeilCompletedGrowth001.lean#L19)

```lean
lemma weighted_integrable {C p : ℝ} (hC : 0≤C) (hp : 0<p)
    (hh : ∀t:ℝ,1≤t→‖modif t‖≤C*Real.exp (-p*t)) (s : ℂ) :
    Integrable (fun u : ℝ=>Real.exp (-s.re*u) • modif (Real.exp (-u)))
```

## `RhWeilCompletedGrowth.mellin_norm_bound`

[RhWeilCompletedGrowth001.lean,line 27](RhWeilCompletedGrowth001.lean#L27)

```lean
lemma mellin_norm_bound {C p : ℝ} (hC : 0≤C) (hp : 0<p)
    (hh : ∀t:ℝ,1≤t→‖modif t‖≤C*Real.exp (-p*t)) (s : ℂ) :
    ‖mellin modif s‖≤(C*gaussianMass p)*Real.exp (2*(|s.re|+1/2)^2/p)
```

## `RhWeilCompletedGrowth.completed_growth`

[RhWeilCompletedGrowth001.lean,line 44](RhWeilCompletedGrowth001.lean#L44)

```lean
theorem completed_growth : ∃B:ℝ,0<B ∧ ∃D:ℝ,0<D ∧
    ∀s:ℂ,‖completedRiemannZeta₀ s‖≤B*Real.exp (D*(1+‖s‖)^2)
```

## `RhWeilTheta.evenKernel_head_bound`

[RhWeilThetaBound001.lean,line 14](RhWeilThetaBound001.lean#L14)

```lean
theorem evenKernel_head_bound :
    ∃ C : ℝ, 0<C ∧ ∃ p : ℝ, 0<p ∧ ∀ t : ℝ, 1≤t →
      |HurwitzZeta.evenKernel 0 t-1|≤C*Real.exp (-p*t)
```

## `RhWeilTheta.fePair_modif_head_bound`

[RhWeilThetaBound001.lean,line 56](RhWeilThetaBound001.lean#L56)

```lean
theorem fePair_modif_head_bound :
    ∃ C : ℝ, 0<C ∧ ∃ p : ℝ, 0<p ∧ ∀ t : ℝ, 1≤t →
      ‖(HurwitzZeta.hurwitzEvenFEPair 0).f_modif t‖≤C*Real.exp (-p*t)
```

## `RhWeilThetaGeometry.modif`

[RhWeilThetaGeometry001.lean,line 14](RhWeilThetaGeometry001.lean#L14)

```lean
def modif (t : ℝ) : ℂ
```

## `RhWeilThetaGeometry.modif_one`

[RhWeilThetaGeometry001.lean,line 16](RhWeilThetaGeometry001.lean#L16)

```lean
lemma modif_one : modif 1=0
```

## `RhWeilThetaGeometry.modif_inv`

[RhWeilThetaGeometry001.lean,line 19](RhWeilThetaGeometry001.lean#L19)

```lean
lemma modif_inv {t : ℝ} (ht : 0<t) :
    modif (1/t)=((t^(1/2:ℝ):ℝ):ℂ)*modif t
```

## `RhWeilThetaGeometry.modif_log_bound`

[RhWeilThetaGeometry001.lean,line 28](RhWeilThetaGeometry001.lean#L28)

```lean
lemma modif_log_bound {C p : ℝ} (hC : 0≤C)
    (hh : ∀t:ℝ,1≤t→‖modif t‖≤C*Real.exp (-p*t)) (u : ℝ) :
    ‖modif (Real.exp (-u))‖≤C*Real.exp (|u|/2-p*Real.exp |u|)
```

## `RhWeilThetaGeometry.square_le_four_exp`

[RhWeilThetaGeometry001.lean,line 48](RhWeilThetaGeometry001.lean#L48)

```lean
lemma square_le_four_exp {x : ℝ} (hx : 0≤x) : x^2≤4*Real.exp x
```

## `RhWeilThetaGeometry.linear_double_exponential_le_gaussian`

[RhWeilThetaGeometry001.lean,line 57](RhWeilThetaGeometry001.lean#L57)

```lean
lemma linear_double_exponential_le_gaussian {p r u : ℝ} (hp : 0<p) :
    r*|u|-p*Real.exp |u|≤2*r^2/p-(p/8)*u^2
```

## `RhWeilThetaGeometry.twisted_gaussian_bound`

[RhWeilThetaGeometry001.lean,line 67](RhWeilThetaGeometry001.lean#L67)

```lean
lemma twisted_gaussian_bound {C p : ℝ} (hC : 0≤C) (hp : 0<p)
    (hh : ∀t:ℝ,1≤t→‖modif t‖≤C*Real.exp (-p*t)) (s : ℂ) (u : ℝ) :
    ‖Real.exp (-s.re*u) • modif (Real.exp (-u))‖≤
      (C*Real.exp (2*(|s.re|+1/2)^2/p))*Real.exp (-(p/8)*u^2)
```

## `RhWeilTheta.theta_exp_continuous`

[RhWeilThetaMeasurable001.lean,line 12](RhWeilThetaMeasurable001.lean#L12)

```lean
lemma theta_exp_continuous :
    Continuous (fun u : ℝ => (HurwitzZeta.evenKernel 0 (Real.exp (-u)):ℂ))
```

## `RhWeilTheta.modif_exp_stronglyMeasurable`

[RhWeilThetaMeasurable001.lean,line 20](RhWeilThetaMeasurable001.lean#L20)

```lean
theorem modif_exp_stronglyMeasurable :
    StronglyMeasurable (fun u : ℝ =>
      (HurwitzZeta.hurwitzEvenFEPair 0).f_modif (Real.exp (-u)))
```

## `RhWeilTheta.weighted_modif_stronglyMeasurable`

[RhWeilThetaMeasurable001.lean,line 46](RhWeilThetaMeasurable001.lean#L46)

```lean
theorem weighted_modif_stronglyMeasurable (s : ℂ) :
    StronglyMeasurable (fun u : ℝ=>Real.exp (-s.re*u) •
      (HurwitzZeta.hurwitzEvenFEPair 0).f_modif (Real.exp (-u)))
```

## `RhWeilTheta.weighted_modif_aestronglyMeasurable`

[RhWeilThetaMeasurable001.lean,line 52](RhWeilThetaMeasurable001.lean#L52)

```lean
theorem weighted_modif_aestronglyMeasurable (s : ℂ) :
    AEStronglyMeasurable (fun u : ℝ=>Real.exp (-s.re*u) •
      (HurwitzZeta.hurwitzEvenFEPair 0).f_modif (Real.exp (-u))) volume
```

## `ThetaMacdonald.Complete.ratio`

[ThetaCompleteRatio.lean,line 21](ThetaCompleteRatio.lean#L21)

```lean
def ratio (u : ℝ) : ℝ
```

## `ThetaMacdonald.Complete.ratioD1`

[ThetaCompleteRatio.lean,line 24](ThetaCompleteRatio.lean#L24)

```lean
def ratioD1 (u : ℝ) : ℝ
```

## `ThetaMacdonald.Complete.ratioD2`

[ThetaCompleteRatio.lean,line 29](ThetaCompleteRatio.lean#L29)

```lean
def ratioD2 (u : ℝ) : ℝ
```

## `ThetaMacdonald.Complete.ratio_eq_source_quotient`

[ThetaCompleteRatio.lean,line 37](ThetaCompleteRatio.lean#L37)

```lean
theorem ratio_eq_source_quotient (u : ℝ) :
    ratio u = (∑' n : ℕ, rawShell (n + 1) u) /
      Real.exp (-(2 * Real.pi * Real.cosh (2 * u)))
```

## `ThetaMacdonald.Complete.hasSum_ratioRaw`

[ThetaCompleteRatio.lean,line 44](ThetaCompleteRatio.lean#L44)

```lean
theorem hasSum_ratioRaw (u : ℝ) :
    HasSum (fun k : ℕ => ratioRaw k u) (ratio u)
```

## `ThetaMacdonald.Complete.hasDerivAt_ratio`

[ThetaCompleteRatio.lean,line 49](ThetaCompleteRatio.lean#L49)

```lean
theorem hasDerivAt_ratio (u : ℝ) :
    HasDerivAt ratio (ratioD1 u) u
```

## `ThetaMacdonald.Complete.hasDerivAt_ratioD1`

[ThetaCompleteRatio.lean,line 57](ThetaCompleteRatio.lean#L57)

```lean
theorem hasDerivAt_ratioD1 (u : ℝ) :
    HasDerivAt ratioD1 (ratioD2 u) u
```

## `ThetaMacdonald.Complete.hasSum_ratioRawD2`

[ThetaCompleteRatio.lean,line 69](ThetaCompleteRatio.lean#L69)

```lean
theorem hasSum_ratioRawD2 (u : ℝ) :
    HasSum (fun k : ℕ => ratioRawD2 k u) (ratioD2 u)
```

## `ThetaMacdonald.Complete.summable_ratioRawD2`

[ThetaCompleteRatio.lean,line 80](ThetaCompleteRatio.lean#L80)

```lean
theorem summable_ratioRawD2 (u : ℝ) :
    Summable (fun k : ℕ => ratioRawD2 k u)
```

## `ThetaMacdonald.Complete.second_deriv_ratio_eq_tsum`

[ThetaCompleteRatio.lean,line 84](ThetaCompleteRatio.lean#L84)

```lean
theorem second_deriv_ratio_eq_tsum (u : ℝ) :
    deriv (deriv ratio) u = ∑' k : ℕ, ratioRawD2 k u
```

## `ThetaMacdonald.Complete.ratioRawD2_zero`

[ThetaCompleteRatio.lean,line 90](ThetaCompleteRatio.lean#L90)

```lean
theorem ratioRawD2_zero (u : ℝ) : ratioRawD2 0 u = 0
```

## `ThetaMacdonald.Complete.second_deriv_ratio_pos`

[ThetaCompleteRatio.lean,line 94](ThetaCompleteRatio.lean#L94)

```lean
theorem second_deriv_ratio_pos {u : ℝ} (hu : 0 ≤ u) :
    0 < deriv (deriv ratio) u
```

## `ThetaMacdonald.Cumulative.densityDifference`

[ThetaCumulativeOrder.lean,line 12](ThetaCumulativeOrder.lean#L12)

```lean
def densityDifference (t : ℝ) : ℝ
```

## `ThetaMacdonald.Cumulative.cumulative`

[ThetaCumulativeOrder.lean,line 13](ThetaCumulativeOrder.lean#L13)

```lean
def cumulative (u : ℝ) : ℝ
```

## `ThetaMacdonald.Cumulative.integrable_densityDifference`

[ThetaCumulativeOrder.lean,line 15](ThetaCumulativeOrder.lean#L15)

```lean
theorem integrable_densityDifference :
    IntegrableOn densityDifference (Ioi (0 : ℝ))
```

## `ThetaMacdonald.Cumulative.integral_densityDifference_zero`

[ThetaCumulativeOrder.lean,line 19](ThetaCumulativeOrder.lean#L19)

```lean
theorem integral_densityDifference_zero :
    (∫ t in Ioi (0 : ℝ), densityDifference t) = 0
```

## `ThetaMacdonald.Cumulative.cumulative_zero`

[ThetaCumulativeOrder.lean,line 25](ThetaCumulativeOrder.lean#L25)

```lean
theorem cumulative_zero : cumulative 0 = 0
```

## `ThetaMacdonald.Cumulative.actual_finite_integrable`

[ThetaCumulativeOrder.lean,line 28](ThetaCumulativeOrder.lean#L28)

```lean
theorem actual_finite_integrable {u : ℝ} (hu : 0 ≤ u) :
    IntervalIntegrable densityDifference volume 0 u
```

## `ThetaMacdonald.Cumulative.actual_tail_integrable`

[ThetaCumulativeOrder.lean,line 32](ThetaCumulativeOrder.lean#L32)

```lean
theorem actual_tail_integrable {u : ℝ} (hu : 0 ≤ u) :
    IntegrableOn densityDifference (Ioi u)
```

## `ThetaMacdonald.Cumulative.cumulative_eq_Ioc`

[ThetaCumulativeOrder.lean,line 36](ThetaCumulativeOrder.lean#L36)

```lean
theorem cumulative_eq_Ioc {u : ℝ} (hu : 0 ≤ u) :
    cumulative u = ∫ t in Ioc (0 : ℝ) u, densityDifference t
```

## `ThetaMacdonald.Cumulative.cumulative_eq_Ioo`

[ThetaCumulativeOrder.lean,line 40](ThetaCumulativeOrder.lean#L40)

```lean
theorem cumulative_eq_Ioo {u : ℝ} (hu : 0 ≤ u) :
    cumulative u = ∫ t in Ioo (0 : ℝ) u, densityDifference t
```

## `ThetaMacdonald.Cumulative.cumulative_eq_Icc`

[ThetaCumulativeOrder.lean,line 44](ThetaCumulativeOrder.lean#L44)

```lean
theorem cumulative_eq_Icc {u : ℝ} (hu : 0 ≤ u) :
    cumulative u = ∫ t in Icc (0 : ℝ) u, densityDifference t
```

## `ThetaMacdonald.Cumulative.actual_head_tail_balance`

[ThetaCumulativeOrder.lean,line 48](ThetaCumulativeOrder.lean#L48)

```lean
theorem actual_head_tail_balance {u : ℝ} (hu : 0 ≤ u) :
    cumulative u + (∫ t in Ioi u, densityDifference t) = 0
```

## `ThetaMacdonald.Cumulative.cumulative_eq_neg_tail`

[ThetaCumulativeOrder.lean,line 54](ThetaCumulativeOrder.lean#L54)

```lean
theorem cumulative_eq_neg_tail {u : ℝ} (hu : 0 ≤ u) :
    cumulative u = -(∫ t in Ioi u, densityDifference t)
```

## `ThetaMacdonald.Cumulative.cumulative_eq_CDF_difference`

[ThetaCumulativeOrder.lean,line 59](ThetaCumulativeOrder.lean#L59)

```lean
theorem cumulative_eq_CDF_difference {u : ℝ} (hu : 0 ≤ u) :
    cumulative u =
      (∫ t in (0 : ℝ)..u, thetaDensity t) -
        (∫ t in (0 : ℝ)..u, macdonaldDensity t)
```

## `ThetaMacdonald.Cumulative.actual_cumulative_order`

[ThetaCumulativeOrder.lean,line 69](ThetaCumulativeOrder.lean#L69)

```lean
theorem actual_cumulative_order {u : ℝ} (hu : 0 < u) :
    cumulative u < 0
```

## `ThetaMacdonald.Cumulative.actual_set_cumulative_order`

[ThetaCumulativeOrder.lean,line 77](ThetaCumulativeOrder.lean#L77)

```lean
theorem actual_set_cumulative_order {u : ℝ} (hu : 0 < u) :
    (∫ t in Icc (0 : ℝ) u, densityDifference t) < 0
```

## `ThetaMacdonald.Cumulative.actual_CDF_strict_order`

[ThetaCumulativeOrder.lean,line 82](ThetaCumulativeOrder.lean#L82)

```lean
theorem actual_CDF_strict_order {u : ℝ} (hu : 0 < u) :
    (∫ t in (0 : ℝ)..u, thetaDensity t) <
      ∫ t in (0 : ℝ)..u, macdonaldDensity t
```

## `ThetaMacdonald.Crossing.integral_Ioi_pos_of_everywhere_pos`

[ThetaDensityCrossing.lean,line 12](ThetaDensityCrossing.lean#L12)

```lean
theorem integral_Ioi_pos_of_everywhere_pos {f : ℝ → ℝ}
    (hi : IntegrableOn f (Ioi (0 : ℝ))) (hp : ∀ u : ℝ, 0 < u → 0 < f u) :
    0 < ∫ u in Ioi (0 : ℝ), f u
```

## `ThetaMacdonald.Crossing.ratio_origin_lt_one`

[ThetaDensityCrossing.lean,line 28](ThetaDensityCrossing.lean#L28)

```lean
theorem ratio_origin_lt_one : likelihoodRatio 0 < 1
```

## `ThetaMacdonald.Crossing.exists_ratio_gt_one`

[ThetaDensityCrossing.lean,line 43](ThetaDensityCrossing.lean#L43)

```lean
theorem exists_ratio_gt_one :
    ∃ u : ℝ, 0 < u ∧ 1 < likelihoodRatio u
```

## `ThetaMacdonald.Crossing.exists_positive_ratio_one`

[ThetaDensityCrossing.lean,line 63](ThetaDensityCrossing.lean#L63)

```lean
theorem exists_positive_ratio_one :
    ∃ c : ℝ, 0 < c ∧ likelihoodRatio c = 1
```

## `ThetaMacdonald.Crossing.unique_density_crossing`

[ThetaDensityCrossing.lean,line 74](ThetaDensityCrossing.lean#L74)

```lean
theorem unique_density_crossing :
    ∃! c : ℝ, 0 < c ∧ thetaDensity c = macdonaldDensity c
```

## `ThetaMacdonald.Crossing.density_crossing_sides`

[ThetaDensityCrossing.lean,line 82](ThetaDensityCrossing.lean#L82)

```lean
theorem density_crossing_sides {c : ℝ} (hc : 0 < c)
    (he : thetaDensity c = macdonaldDensity c) :
    (∀ u : ℝ, 0 ≤ u → u < c → thetaDensity u < macdonaldDensity u) ∧
    (∀ u : ℝ, c < u → macdonaldDensity u < thetaDensity u)
```

## `ThetaMacdonald.Crossing.density_eq_iff_crossing`

[ThetaDensityCrossing.lean,line 97](ThetaDensityCrossing.lean#L97)

```lean
theorem density_eq_iff_crossing {c : ℝ} (hc : 0 < c)
    (he : thetaDensity c = macdonaldDensity c) {u : ℝ} (hu : 0 ≤ u) :
    thetaDensity u = macdonaldDensity u ↔ u = c
```

## `ThetaMacdonald.Crossing.actual_density_crossing`

[ThetaDensityCrossing.lean,line 108](ThetaDensityCrossing.lean#L108)

```lean
theorem actual_density_crossing :
    ∃ c : ℝ, 0 < c ∧ thetaDensity c = macdonaldDensity c ∧
      (∀ u : ℝ, 0 ≤ u → u < c → thetaDensity u < macdonaldDensity u) ∧
      (∀ u : ℝ, c < u → macdonaldDensity u < thetaDensity u) ∧
      (∀ u : ℝ, 0 ≤ u →
        (thetaDensity u = macdonaldDensity u ↔ u = c))
```

## `ThetaMacdonald.Crossing.ratioScale`

[ThetaDensityRatio.lean,line 10](ThetaDensityRatio.lean#L10)

```lean
def ratioScale : ℝ
```

## `ThetaMacdonald.Crossing.likelihoodRatio`

[ThetaDensityRatio.lean,line 11](ThetaDensityRatio.lean#L11)

```lean
def likelihoodRatio (u : ℝ) : ℝ
```

## `ThetaMacdonald.Crossing.ratioScale_pos`

[ThetaDensityRatio.lean,line 13](ThetaDensityRatio.lean#L13)

```lean
theorem ratioScale_pos : 0 < ratioScale
```

## `ThetaMacdonald.Crossing.likelihoodRatio_eq_density_div`

[ThetaDensityRatio.lean,line 17](ThetaDensityRatio.lean#L17)

```lean
theorem likelihoodRatio_eq_density_div (u : ℝ) :
    likelihoodRatio u = thetaDensity u/macdonaldDensity u
```

## `ThetaMacdonald.Crossing.continuous_likelihoodRatio`

[ThetaDensityRatio.lean,line 28](ThetaDensityRatio.lean#L28)

```lean
theorem continuous_likelihoodRatio : Continuous likelihoodRatio
```

## `ThetaMacdonald.Crossing.strictMonoOn_likelihoodRatio`

[ThetaDensityRatio.lean,line 33](ThetaDensityRatio.lean#L33)

```lean
theorem strictMonoOn_likelihoodRatio :
    StrictMonoOn likelihoodRatio (Ici (0 : ℝ))
```

## `ThetaMacdonald.Crossing.ratio_lt_one_iff`

[ThetaDensityRatio.lean,line 39](ThetaDensityRatio.lean#L39)

```lean
theorem ratio_lt_one_iff (u : ℝ) :
    likelihoodRatio u < 1 ↔ thetaDensity u < macdonaldDensity u
```

## `ThetaMacdonald.Crossing.one_lt_ratio_iff`

[ThetaDensityRatio.lean,line 43](ThetaDensityRatio.lean#L43)

```lean
theorem one_lt_ratio_iff (u : ℝ) :
    1 < likelihoodRatio u ↔ macdonaldDensity u < thetaDensity u
```

## `ThetaMacdonald.Crossing.ratio_eq_one_iff`

[ThetaDensityRatio.lean,line 47](ThetaDensityRatio.lean#L47)

```lean
theorem ratio_eq_one_iff (u : ℝ) :
    likelihoodRatio u = 1 ↔ thetaDensity u = macdonaldDensity u
```

## `ThetaMacdonald.Symmetry.gaussianSeed`

[ThetaGaussianSeed.lean,line 14](ThetaGaussianSeed.lean#L14)

```lean
def gaussianSeed (k : ℕ) (u : ℝ) : ℝ
```

## `ThetaMacdonald.Symmetry.gaussianSeedD1`

[ThetaGaussianSeed.lean,line 16](ThetaGaussianSeed.lean#L16)

```lean
def gaussianSeedD1 (k : ℕ) (u : ℝ) : ℝ
```

## `ThetaMacdonald.Symmetry.gaussianSeedD2`

[ThetaGaussianSeed.lean,line 18](ThetaGaussianSeed.lean#L18)

```lean
def gaussianSeedD2 (k : ℕ) (u : ℝ) : ℝ
```

## `ThetaMacdonald.Symmetry.seedCoefficient`

[ThetaGaussianSeed.lean,line 21](ThetaGaussianSeed.lean#L21)

```lean
def seedCoefficient : ℕ → ℕ → ℝ
  | 0, 0 => 1
  | 1, 0 => 1/2
  | 1, 1 => -2
  | 2, 0 => 1/4
  | 2, 1 => -6
  | 2, 2 => 4
  | _, _ => 0
def seedRow (r k : ℕ) (u : ℝ) : ℝ
```

## `ThetaMacdonald.Symmetry.seedRow`

[ThetaGaussianSeed.lean,line 29](ThetaGaussianSeed.lean#L29)

```lean
def seedRow (r k : ℕ) (u : ℝ) : ℝ
```

## `ThetaMacdonald.Symmetry.seedMajorant`

[ThetaGaussianSeed.lean,line 31](ThetaGaussianSeed.lean#L31)

```lean
def seedMajorant (r : ℕ) (L U : ℝ) (k : ℕ) : ℝ
```

## `ThetaMacdonald.Symmetry.seedRow_zero`

[ThetaGaussianSeed.lean,line 34](ThetaGaussianSeed.lean#L34)

```lean
theorem seedRow_zero (k : ℕ) (u : ℝ) :
    seedRow 0 k u = gaussianSeed k u
```

## `ThetaMacdonald.Symmetry.seedRow_one`

[ThetaGaussianSeed.lean,line 38](ThetaGaussianSeed.lean#L38)

```lean
theorem seedRow_one (k : ℕ) (u : ℝ) :
    seedRow 1 k u = gaussianSeedD1 k u
```

## `ThetaMacdonald.Symmetry.seedRow_two`

[ThetaGaussianSeed.lean,line 43](ThetaGaussianSeed.lean#L43)

```lean
theorem seedRow_two (k : ℕ) (u : ℝ) :
    seedRow 2 k u = gaussianSeedD2 k u
```

## `ThetaMacdonald.Symmetry.summable_seedMajorant`

[ThetaGaussianSeed.lean,line 49](ThetaGaussianSeed.lean#L49)

```lean
theorem summable_seedMajorant (r : ℕ) (L U : ℝ) :
    Summable (seedMajorant r L U)
```

## `ThetaMacdonald.Symmetry.norm_seedRow_le`

[ThetaGaussianSeed.lean,line 52](ThetaGaussianSeed.lean#L52)

```lean
theorem norm_seedRow_le (r k : ℕ) {L U u : ℝ} (hu : u ∈ Icc L U) :
    ‖seedRow r k u‖ ≤ seedMajorant r L U k
```

## `ThetaMacdonald.Symmetry.summable_seedRow`

[ThetaGaussianSeed.lean,line 55](ThetaGaussianSeed.lean#L55)

```lean
theorem summable_seedRow (r : ℕ) (u : ℝ) :
    Summable (fun k => seedRow r k u)
```

## `ThetaMacdonald.Symmetry.summable_gaussianSeed`

[ThetaGaussianSeed.lean,line 59](ThetaGaussianSeed.lean#L59)

```lean
theorem summable_gaussianSeed (u : ℝ) :
    Summable (fun k => gaussianSeed k u)
```

## `ThetaMacdonald.Symmetry.summable_gaussianSeedD1`

[ThetaGaussianSeed.lean,line 62](ThetaGaussianSeed.lean#L62)

```lean
theorem summable_gaussianSeedD1 (u : ℝ) :
    Summable (fun k => gaussianSeedD1 k u)
```

## `ThetaMacdonald.Symmetry.summable_gaussianSeedD2`

[ThetaGaussianSeed.lean,line 65](ThetaGaussianSeed.lean#L65)

```lean
theorem summable_gaussianSeedD2 (u : ℝ) :
    Summable (fun k => gaussianSeedD2 k u)
```

## `ThetaMacdonald.Symmetry.hasDerivAt_gaussianSeed`

[ThetaGaussianSeed.lean,line 69](ThetaGaussianSeed.lean#L69)

```lean
theorem hasDerivAt_gaussianSeed (k : ℕ) (u : ℝ) :
    HasDerivAt (gaussianSeed k) (gaussianSeedD1 k u) u
```

## `ThetaMacdonald.Symmetry.hasDerivAt_gaussianSeedD1`

[ThetaGaussianSeed.lean,line 75](ThetaGaussianSeed.lean#L75)

```lean
theorem hasDerivAt_gaussianSeedD1 (k : ℕ) (u : ℝ) :
    HasDerivAt (gaussianSeedD1 k) (gaussianSeedD2 k u) u
```

## `ThetaMacdonald.Symmetry.hasDerivAt_tsum_gaussianSeed`

[ThetaGaussianSeed.lean,line 83](ThetaGaussianSeed.lean#L83)

```lean
theorem hasDerivAt_tsum_gaussianSeed (u : ℝ) :
    HasDerivAt (fun v => ∑' k, gaussianSeed k v)
      (∑' k, gaussianSeedD1 k u) u
```

## `ThetaMacdonald.Symmetry.hasDerivAt_tsum_gaussianSeedD1`

[ThetaGaussianSeed.lean,line 94](ThetaGaussianSeed.lean#L94)

```lean
theorem hasDerivAt_tsum_gaussianSeedD1 (u : ℝ) :
    HasDerivAt (fun v => ∑' k, gaussianSeedD1 k v)
      (∑' k, gaussianSeedD2 k u) u
```

## `ThetaMacdonald.Symmetry.gaussianSum`

[ThetaGaussianSeed.lean,line 105](ThetaGaussianSeed.lean#L105)

```lean
def gaussianSum (u : ℝ) : ℝ
```

## `ThetaMacdonald.Symmetry.centeredTheta`

[ThetaGaussianSeed.lean,line 106](ThetaGaussianSeed.lean#L106)

```lean
def centeredTheta (u : ℝ) : ℝ
```

## `ThetaMacdonald.Symmetry.centeredThetaD1`

[ThetaGaussianSeed.lean,line 107](ThetaGaussianSeed.lean#L107)

```lean
def centeredThetaD1 (u : ℝ) : ℝ
```

## `ThetaMacdonald.Symmetry.centeredThetaD2`

[ThetaGaussianSeed.lean,line 109](ThetaGaussianSeed.lean#L109)

```lean
def centeredThetaD2 (u : ℝ) : ℝ
```

## `ThetaMacdonald.Symmetry.hasDerivAt_centeredTheta`

[ThetaGaussianSeed.lean,line 112](ThetaGaussianSeed.lean#L112)

```lean
theorem hasDerivAt_centeredTheta (u : ℝ) :
    HasDerivAt centeredTheta (centeredThetaD1 u) u
```

## `ThetaMacdonald.Symmetry.hasDerivAt_centeredThetaD1`

[ThetaGaussianSeed.lean,line 119](ThetaGaussianSeed.lean#L119)

```lean
theorem hasDerivAt_centeredThetaD1 (u : ℝ) :
    HasDerivAt centeredThetaD1 (centeredThetaD2 u) u
```

## `ThetaMacdonald.Symmetry.deriv_centeredTheta`

[ThetaGaussianSeed.lean,line 126](ThetaGaussianSeed.lean#L126)

```lean
theorem deriv_centeredTheta :
    deriv centeredTheta = centeredThetaD1
```

## `ThetaMacdonald.Symmetry.second_deriv_centeredTheta`

[ThetaGaussianSeed.lean,line 129](ThetaGaussianSeed.lean#L129)

```lean
theorem second_deriv_centeredTheta (u : ℝ) :
    deriv (deriv centeredTheta) u = centeredThetaD2 u
```

## `ThetaMacdonald.Symmetry.rawShell_eq_seed_derivatives`

[ThetaGaussianSeed.lean,line 134](ThetaGaussianSeed.lean#L134)

```lean
theorem rawShell_eq_seed_derivatives (k : ℕ) (u : ℝ) :
    rawShell k u = 2 * gaussianSeedD2 k u - (1/2 : ℝ) * gaussianSeed k u
```

## `ThetaMacdonald.Symmetry.raw_sum_eq_centeredTheta`

[ThetaGaussianSeed.lean,line 138](ThetaGaussianSeed.lean#L138)

```lean
theorem raw_sum_eq_centeredTheta (u : ℝ) :
    (∑' k : ℕ, rawShell k u) =
      deriv (deriv centeredTheta) u - centeredTheta u / 4
```

## `ThetaMacdonald.Density.thetaProfile`

[ThetaMassBounds.lean,line 13](ThetaMassBounds.lean#L13)

```lean
def thetaProfile (u : ℝ) : ℝ
```

## `ThetaMacdonald.Density.thetaMass`

[ThetaMassBounds.lean,line 14](ThetaMassBounds.lean#L14)

```lean
def thetaMass : ℝ
```

## `ThetaMacdonald.Density.thetaTailWeight`

[ThetaMassBounds.lean,line 15](ThetaMassBounds.lean#L15)

```lean
def thetaTailWeight (k : ℕ) : ℝ
```

## `ThetaMacdonald.Density.thetaTailConstant`

[ThetaMassBounds.lean,line 17](ThetaMassBounds.lean#L17)

```lean
def thetaTailConstant : ℝ
```

## `ThetaMacdonald.Density.rawShell_nonneg`

[ThetaMassBounds.lean,line 19](ThetaMassBounds.lean#L19)

```lean
theorem rawShell_nonneg {u : ℝ} (hu : 0 ≤ u) (k : ℕ) :
    0 ≤ rawShell k u
```

## `ThetaMacdonald.Density.rawShell_tail_bound`

[ThetaMassBounds.lean,line 26](ThetaMassBounds.lean#L26)

```lean
theorem rawShell_tail_bound {u : ℝ} (hu : 0 ≤ u) (k : ℕ) :
    ‖rawShell k u‖ ≤ thetaTailWeight k * Real.exp (-u)
```

## `ThetaMacdonald.Density.summable_thetaTailWeight`

[ThetaMassBounds.lean,line 72](ThetaMassBounds.lean#L72)

```lean
theorem summable_thetaTailWeight : Summable thetaTailWeight
```

## `ThetaMacdonald.Density.thetaProfile_tail_bound`

[ThetaMassBounds.lean,line 80](ThetaMassBounds.lean#L80)

```lean
theorem thetaProfile_tail_bound {u : ℝ} (hu : 0 ≤ u) :
    ‖thetaProfile u‖ ≤ thetaTailConstant * Real.exp (-u)
```

## `ThetaMacdonald.Density.thetaProfile_pos`

[ThetaMassBounds.lean,line 92](ThetaMassBounds.lean#L92)

```lean
theorem thetaProfile_pos {u : ℝ} (hu : 0 ≤ u) :
    0 < thetaProfile u
```

## `ThetaMacdonald.Density.integrable_thetaProfile`

[ThetaMassBounds.lean,line 97](ThetaMassBounds.lean#L97)

```lean
theorem integrable_thetaProfile :
    IntegrableOn thetaProfile (Ioi (0 : ℝ))
```

## `ThetaMacdonald.Density.thetaMass_pos`

[ThetaMassBounds.lean,line 107](ThetaMassBounds.lean#L107)

```lean
theorem thetaMass_pos : 0 < thetaMass
```

## `ThetaMacdonald.Mass.logTheta`

[ThetaMellinMass.lean,line 13](ThetaMellinMass.lean#L13)

```lean
def logTheta (v : ℝ) : ℂ
```

## `ThetaMacdonald.Mass.integrable_logTheta`

[ThetaMellinMass.lean,line 16](ThetaMellinMass.lean#L16)

```lean
theorem integrable_logTheta : Integrable logTheta
```

## `ThetaMacdonald.Mass.logTheta_even`

[ThetaMellinMass.lean,line 26](ThetaMellinMass.lean#L26)

```lean
theorem logTheta_even (v : ℝ) : logTheta (-v) = logTheta v
```

## `ThetaMacdonald.Mass.seedTail_hurwitz`

[ThetaMellinMass.lean,line 38](ThetaMellinMass.lean#L38)

```lean
theorem seedTail_hurwitz (u : ℝ) :
    seedTail u = Real.exp (u/2)*
      (HurwitzZeta.evenKernel 0 (Real.exp (2*u))-1)/2
```

## `ThetaMacdonald.Mass.logTheta_neg_of_pos`

[ThetaMellinMass.lean,line 62](ThetaMellinMass.lean#L62)

```lean
theorem logTheta_neg_of_pos {v : ℝ} (hv : 0 < v) :
    logTheta (-v) = ((2*seedTail (v/2) : ℝ) : ℂ)
```

## `ThetaMacdonald.Mass.logTheta_pos`

[ThetaMellinMass.lean,line 75](ThetaMellinMass.lean#L75)

```lean
theorem logTheta_pos {v : ℝ} (hv : 0 < v) :
    logTheta v = ((2*seedTail (v/2) : ℝ) : ℂ)
```

## `ThetaMacdonald.Mass.logTheta_half_integral_re`

[ThetaMellinMass.lean,line 79](ThetaMellinMass.lean#L79)

```lean
theorem logTheta_half_integral_re :
    (∫ v in Ioi (0 : ℝ), logTheta v).re =
      4*(∫ u in Ioi (0 : ℝ), seedTail u)
```

## `ThetaMacdonald.Mass.completed_half_log`

[ThetaMellinMass.lean,line 105](ThetaMellinMass.lean#L105)

```lean
theorem completed_half_log :
    completedRiemannZeta₀ (1/2 : ℂ) = (∫ v : ℝ, logTheta v)/2
```

## `ThetaMacdonald.Mass.completed_half_real`

[ThetaMellinMass.lean,line 120](ThetaMellinMass.lean#L120)

```lean
theorem completed_half_real :
    (completedRiemannZeta₀ (1/2 : ℂ)).re =
      4*(∫ u in Ioi (0 : ℝ), seedTail u)
```

## `ThetaMacdonald.Mass.gamma0`

[ThetaMellinMass.lean,line 140](ThetaMellinMass.lean#L140)

```lean
def gamma0 : ℝ
```

## `ThetaMacdonald.Mass.thetaMass_eq_gamma0`

[ThetaMellinMass.lean,line 143](ThetaMellinMass.lean#L143)

```lean
theorem thetaMass_eq_gamma0 : thetaMass = gamma0
```

## `ThetaMacdonald.Mass.gamma0_pos`

[ThetaMellinMass.lean,line 150](ThetaMellinMass.lean#L150)

```lean
theorem gamma0_pos : 0 < gamma0
```

## `ThetaMacdonald.Moment.integrable_theta_power`

[ThetaMomentOrder.lean,line 11](ThetaMomentOrder.lean#L11)

```lean
theorem integrable_theta_power (n : ℕ) :
    IntegrableOn (fun u : ℝ => u^n*thetaDensity u) (Ioi (0 : ℝ))
```

## `ThetaMacdonald.Moment.integrable_macdonald_power`

[ThetaMomentOrder.lean,line 16](ThetaMomentOrder.lean#L16)

```lean
theorem integrable_macdonald_power (n : ℕ) :
    IntegrableOn (fun u : ℝ => u^n*macdonaldDensity u) (Ioi (0 : ℝ))
```

## `ThetaMacdonald.Moment.integrable_difference_power`

[ThetaMomentOrder.lean,line 21](ThetaMomentOrder.lean#L21)

```lean
theorem integrable_difference_power (n : ℕ) :
    IntegrableOn (fun u : ℝ => u^n*densityDifference u) (Ioi (0 : ℝ))
```

## `ThetaMacdonald.Moment.actual_monotone_weight_order`

[ThetaMomentOrder.lean,line 28](ThetaMomentOrder.lean#L28)

```lean
theorem actual_monotone_weight_order {w : ℝ → ℝ}
    (hwm : IntegrableOn (fun u => w u*thetaDensity u) (Ioi (0 : ℝ)))
    (hwn : IntegrableOn (fun u => w u*macdonaldDensity u) (Ioi (0 : ℝ)))
    (hw : MonotoneOn w (Ioi (0 : ℝ)))
    (hstrict : ∀ c : ℝ, 0 < c → ∃ b : ℝ, c < b ∧ w c < w b) :
    (∫ u in Ioi (0 : ℝ), w u*macdonaldDensity u) <
      ∫ u in Ioi (0 : ℝ), w u*thetaDensity u
```

## `ThetaMacdonald.Moment.actual_power_moment_order`

[ThetaMomentOrder.lean,line 42](ThetaMomentOrder.lean#L42)

```lean
theorem actual_power_moment_order (n : ℕ) (hn : 0 < n) :
    (∫ u in Ioi (0 : ℝ), u^n*macdonaldDensity u) <
      ∫ u in Ioi (0 : ℝ), u^n*thetaDensity u
```

## `ThetaMacdonald.Moment.actual_positive_even_moment_order`

[ThetaMomentOrder.lean,line 52](ThetaMomentOrder.lean#L52)

```lean
theorem actual_positive_even_moment_order (j : ℕ) (hj : 0 < j) :
    (∫ u in Ioi (0 : ℝ), u^(2*j)*macdonaldDensity u) <
      ∫ u in Ioi (0 : ℝ), u^(2*j)*thetaDensity u
```

## `ThetaMacdonald.Moment.actual_zeroth_moment_equal`

[ThetaMomentOrder.lean,line 57](ThetaMomentOrder.lean#L57)

```lean
theorem actual_zeroth_moment_equal :
    (∫ u in Ioi (0 : ℝ), u^0*macdonaldDensity u) =
      ∫ u in Ioi (0 : ℝ), u^0*thetaDensity u
```

## `ThetaMacdonald.referenceWeight`

[ThetaOrderCore.lean,line 12](ThetaOrderCore.lean#L12)

```lean
def referenceWeight (u : ℝ) : ℝ
```

## `ThetaMacdonald.ratioRaw`

[ThetaOrderCore.lean,line 13](ThetaOrderCore.lean#L13)

```lean
def ratioRaw (k : ℕ) (u : ℝ) : ℝ
```

## `ThetaMacdonald.ratioRawD1`

[ThetaOrderCore.lean,line 14](ThetaOrderCore.lean#L14)

```lean
def ratioRawD1 (k : ℕ) (u : ℝ) : ℝ
```

## `ThetaMacdonald.ratioRawD2`

[ThetaOrderCore.lean,line 17](ThetaOrderCore.lean#L17)

```lean
def ratioRawD2 (k : ℕ) (u : ℝ) : ℝ
```

## `ThetaMacdonald.hasDerivAt_shellT`

[ThetaOrderCore.lean,line 22](ThetaOrderCore.lean#L22)

```lean
theorem hasDerivAt_shellT (u : ℝ) :
    HasDerivAt shellT (2 * shellT u) u
```

## `ThetaMacdonald.hasDerivAt_shellW`

[ThetaOrderCore.lean,line 29](ThetaOrderCore.lean#L29)

```lean
theorem hasDerivAt_shellW (u : ℝ) :
    HasDerivAt shellW (-2 * shellW u) u
```

## `ThetaMacdonald.hasDerivAt_referenceWeight`

[ThetaOrderCore.lean,line 38](ThetaOrderCore.lean#L38)

```lean
theorem hasDerivAt_referenceWeight (u : ℝ) :
    HasDerivAt referenceWeight
      ((2 * shellT u - 2 * shellW u) * referenceWeight u) u
```

## `ThetaMacdonald.hasDerivAt_ratioRaw`

[ThetaOrderCore.lean,line 46](ThetaOrderCore.lean#L46)

```lean
theorem hasDerivAt_ratioRaw (k : ℕ) (u : ℝ) :
    HasDerivAt (ratioRaw k) (ratioRawD1 k u) u
```

## `ThetaMacdonald.hasDerivAt_ratioRawD1`

[ThetaOrderCore.lean,line 53](ThetaOrderCore.lean#L53)

```lean
theorem hasDerivAt_ratioRawD1 (k : ℕ) (u : ℝ) :
    HasDerivAt (ratioRawD1 k) (ratioRawD2 k u) u
```

## `ThetaMacdonald.referenceWeight_eq_cosh`

[ThetaOrderCore.lean,line 64](ThetaOrderCore.lean#L64)

```lean
theorem referenceWeight_eq_cosh (u : ℝ) :
    referenceWeight u = Real.exp (2 * Real.pi * Real.cosh (2*u))
```

## `ThetaMacdonald.rawShell_pos`

[ThetaOrderCore.lean,line 71](ThetaOrderCore.lean#L71)

```lean
theorem rawShell_pos {k : ℕ} (hk : 1 ≤ k) {u : ℝ} (hu : 0 ≤ u) :
    0 < rawShell k u
```

## `ThetaMacdonald.ratioRaw_pos`

[ThetaOrderCore.lean,line 85](ThetaOrderCore.lean#L85)

```lean
theorem ratioRaw_pos {k : ℕ} (hk : 1 ≤ k) {u : ℝ} (hu : 0 ≤ u) :
    0 < ratioRaw k u
```

## `ThetaMacdonald.ratioRawD2_eq_factor`

[ThetaOrderCore.lean,line 89](ThetaOrderCore.lean#L89)

```lean
theorem ratioRawD2_eq_factor {k : ℕ} {u : ℝ}
    (hd : 2 * shellZ k u - 3 ≠ 0) :
    ratioRawD2 k u = ratioRaw k u *
      (logSlope (shellZ k u) (shellT u) (shellW u)^2 +
        slopeDerivative (shellZ k u) (shellT u) (shellW u))
```

## `ThetaMacdonald.ratioRawD2_pos`

[ThetaOrderCore.lean,line 122](ThetaOrderCore.lean#L122)

```lean
theorem ratioRawD2_pos {k : ℕ} (hk : 1 ≤ k) {u : ℝ} (hu : 0 ≤ u) :
    0 < ratioRawD2 k u
```

## `ThetaMacdonald.deriv_ratioRaw`

[ThetaOrderCore.lean,line 134](ThetaOrderCore.lean#L134)

```lean
theorem deriv_ratioRaw (k : ℕ) : deriv (ratioRaw k) = ratioRawD1 k
```

## `ThetaMacdonald.second_derivative_ratioRaw_pos`

[ThetaOrderCore.lean,line 137](ThetaOrderCore.lean#L137)

```lean
theorem second_derivative_ratioRaw_pos {k : ℕ} (hk : 1 ≤ k) {u : ℝ}
    (hu : 0 ≤ u) :
    0 < deriv (deriv (ratioRaw k)) u
```

## `ThetaMacdonald.Symmetry.gaussianSeed_zero`

[ThetaOriginStationarity.lean,line 15](ThetaOriginStationarity.lean#L15)

```lean
theorem gaussianSeed_zero (u : ℝ) :
    gaussianSeed 0 u = Real.exp (u/2)
```

## `ThetaMacdonald.Symmetry.centeredTheta_eq_full`

[ThetaOriginStationarity.lean,line 19](ThetaOriginStationarity.lean#L19)

```lean
theorem centeredTheta_eq_full (u : ℝ) :
    centeredTheta u = Reflection.centeredFullTheta u
```

## `ThetaMacdonald.Symmetry.centeredTheta_even`

[ThetaOriginStationarity.lean,line 59](ThetaOriginStationarity.lean#L59)

```lean
theorem centeredTheta_even (u : ℝ) :
    centeredTheta (-u) = centeredTheta u
```

## `ThetaMacdonald.Symmetry.raw_sum_even`

[ThetaOriginStationarity.lean,line 64](ThetaOriginStationarity.lean#L64)

```lean
theorem raw_sum_even (u : ℝ) :
    (∑' k : ℕ, rawShell k (-u)) = ∑' k : ℕ, rawShell k u
```

## `ThetaMacdonald.Symmetry.referenceWeight_even`

[ThetaOriginStationarity.lean,line 70](ThetaOriginStationarity.lean#L70)

```lean
theorem referenceWeight_even (u : ℝ) :
    referenceWeight (-u) = referenceWeight u
```

## `ThetaMacdonald.Symmetry.ratio_even`

[ThetaOriginStationarity.lean,line 75](ThetaOriginStationarity.lean#L75)

```lean
theorem ratio_even (u : ℝ) :
    Complete.ratio (-u) = Complete.ratio u
```

## `ThetaMacdonald.Symmetry.tsum_rawShellD1_zero`

[ThetaOriginStationarity.lean,line 82](ThetaOriginStationarity.lean#L82)

```lean
theorem tsum_rawShellD1_zero :
    (∑' k : ℕ, rawShellD1 k 0) = 0
```

## `ThetaMacdonald.Symmetry.deriv_ratio_zero`

[ThetaOriginStationarity.lean,line 88](ThetaOriginStationarity.lean#L88)

```lean
theorem deriv_ratio_zero : deriv Complete.ratio 0 = 0
```

## `ThetaMacdonald.Symmetry.hasDerivAt_ratio_origin`

[ThetaOriginStationarity.lean,line 91](ThetaOriginStationarity.lean#L91)

```lean
theorem hasDerivAt_ratio_origin :
    HasDerivAt Complete.ratio 0 0
```

## `ThetaMacdonald.Reflection.fullTheta`

[ThetaPoissonReflection.lean,line 16](ThetaPoissonReflection.lean#L16)

```lean
def fullTheta (u : ℝ) : ℝ
```

## `ThetaMacdonald.Reflection.centeredFullTheta`

[ThetaPoissonReflection.lean,line 19](ThetaPoissonReflection.lean#L19)

```lean
def centeredFullTheta (u : ℝ) : ℝ
```

## `ThetaMacdonald.Reflection.exp_half_rpow`

[ThetaPoissonReflection.lean,line 22](ThetaPoissonReflection.lean#L22)

```lean
theorem exp_half_rpow (u : ℝ) :
    Real.exp (2 * u) ^ (1 / 2 : ℝ) = Real.exp u
```

## `ThetaMacdonald.Reflection.fullTheta_poisson`

[ThetaPoissonReflection.lean,line 28](ThetaPoissonReflection.lean#L28)

```lean
theorem fullTheta_poisson (u : ℝ) :
    fullTheta u = Real.exp (-u) * fullTheta (-u)
```

## `ThetaMacdonald.Reflection.centeredFullTheta_even`

[ThetaPoissonReflection.lean,line 42](ThetaPoissonReflection.lean#L42)

```lean
theorem centeredFullTheta_even (u : ℝ) :
    centeredFullTheta (-u) = centeredFullTheta u
```

## `ThetaMacdonald.Reflection.deriv_odd_of_even`

[ThetaPoissonReflection.lean,line 52](ThetaPoissonReflection.lean#L52)

```lean
theorem deriv_odd_of_even {f : ℝ → ℝ}
    (hf : ∀ x, f (-x) = f x) (x : ℝ) :
    deriv f (-x) = -deriv f x
```

## `ThetaMacdonald.Reflection.second_deriv_even_of_even`

[ThetaPoissonReflection.lean,line 60](ThetaPoissonReflection.lean#L60)

```lean
theorem second_deriv_even_of_even {f : ℝ → ℝ}
    (hf : ∀ x, f (-x) = f x) (x : ℝ) :
    deriv (deriv f) (-x) = deriv (deriv f) x
```

## `ThetaMacdonald.Reflection.deriv_zero_of_even`

[ThetaPoissonReflection.lean,line 70](ThetaPoissonReflection.lean#L70)

```lean
theorem deriv_zero_of_even {f : ℝ → ℝ}
    (hf : ∀ x, f (-x) = f x) : deriv f 0 = 0
```

## `ThetaMacdonald.Reflection.centeredFullTheta_second_deriv_even`

[ThetaPoissonReflection.lean,line 76](ThetaPoissonReflection.lean#L76)

```lean
theorem centeredFullTheta_second_deriv_even (u : ℝ) :
    deriv (deriv centeredFullTheta) (-u) =
      deriv (deriv centeredFullTheta) u
```

## `ThetaMacdonald.Reflection.centeredFullTheta_deriv_zero`

[ThetaPoissonReflection.lean,line 81](ThetaPoissonReflection.lean#L81)

```lean
theorem centeredFullTheta_deriv_zero :
    deriv centeredFullTheta 0 = 0
```

## `ThetaMacdonald.Slope.hasDerivAt_deriv_ratio`

[ThetaPositiveSlope.lean,line 15](ThetaPositiveSlope.lean#L15)

```lean
theorem hasDerivAt_deriv_ratio (u : ℝ) :
    HasDerivAt (deriv Complete.ratio) (Complete.ratioD2 u) u
```

## `ThetaMacdonald.Slope.strictMonoOn_deriv_ratio`

[ThetaPositiveSlope.lean,line 23](ThetaPositiveSlope.lean#L23)

```lean
theorem strictMonoOn_deriv_ratio :
    StrictMonoOn (deriv Complete.ratio) (Ici (0 : ℝ))
```

## `ThetaMacdonald.Slope.deriv_ratio_pos`

[ThetaPositiveSlope.lean,line 32](ThetaPositiveSlope.lean#L32)

```lean
theorem deriv_ratio_pos {u : ℝ} (hu : 0 < u) :
    0 < deriv Complete.ratio u
```

## `ThetaMacdonald.Mass.xiHalf`

[ThetaProbabilityMass.lean,line 13](ThetaProbabilityMass.lean#L13)

```lean
def xiHalf : ℂ
```

## `ThetaMacdonald.Mass.xiHalf_eq_entire`

[ThetaProbabilityMass.lean,line 17](ThetaProbabilityMass.lean#L17)

```lean
theorem xiHalf_eq_entire :
    xiHalf =
      (1+(1/2 : ℂ)*((1/2 : ℂ)-1)*completedRiemannZeta₀ (1/2 : ℂ))/2
```

## `ThetaMacdonald.Mass.logTheta_im_zero`

[ThetaProbabilityMass.lean,line 32](ThetaProbabilityMass.lean#L32)

```lean
theorem logTheta_im_zero (v : ℝ) : (logTheta v).im = 0
```

## `ThetaMacdonald.Mass.completed_half_im_zero`

[ThetaProbabilityMass.lean,line 40](ThetaProbabilityMass.lean#L40)

```lean
theorem completed_half_im_zero :
    (completedRiemannZeta₀ (1/2 : ℂ)).im = 0
```

## `ThetaMacdonald.Mass.xiHalf_eq_gamma0`

[ThetaProbabilityMass.lean,line 48](ThetaProbabilityMass.lean#L48)

```lean
theorem xiHalf_eq_gamma0 : xiHalf = (gamma0 : ℂ)
```

## `ThetaMacdonald.Mass.thetaMass_eq_xiHalf`

[ThetaProbabilityMass.lean,line 55](ThetaProbabilityMass.lean#L55)

```lean
theorem thetaMass_eq_xiHalf : (thetaMass : ℂ) = xiHalf
```

## `ThetaMacdonald.Mass.thetaDensity`

[ThetaProbabilityMass.lean,line 58](ThetaProbabilityMass.lean#L58)

```lean
def thetaDensity (u : ℝ) : ℝ
```

## `ThetaMacdonald.Mass.integrable_thetaDensity`

[ThetaProbabilityMass.lean,line 60](ThetaProbabilityMass.lean#L60)

```lean
theorem integrable_thetaDensity :
    IntegrableOn thetaDensity (Ioi (0 : ℝ))
```

## `ThetaMacdonald.Mass.thetaDensity_pos`

[ThetaProbabilityMass.lean,line 64](ThetaProbabilityMass.lean#L64)

```lean
theorem thetaDensity_pos {u : ℝ} (hu : 0 ≤ u) :
    0 < thetaDensity u
```

## `ThetaMacdonald.Mass.thetaDensity_mass`

[ThetaProbabilityMass.lean,line 68](ThetaProbabilityMass.lean#L68)

```lean
theorem thetaDensity_mass :
    (∫ u in Ioi (0 : ℝ), thetaDensity u) = 1
```

## `ThetaMacdonald.Mass.thetaDensity_mass_closed`

[ThetaProbabilityMass.lean,line 76](ThetaProbabilityMass.lean#L76)

```lean
theorem thetaDensity_mass_closed :
    (∫ u in Ici (0 : ℝ), thetaDensity u) = 1
```

## `ThetaMacdonald.Mass.actual_equal_probability_masses`

[ThetaProbabilityMass.lean,line 80](ThetaProbabilityMass.lean#L80)

```lean
theorem actual_equal_probability_masses :
    (∫ u in Ici (0 : ℝ), thetaDensity u) =
      ∫ u in Ici (0 : ℝ), macdonaldDensity u
```

## `ThetaMacdonald.SecondMoment.thetaMajorant`

[ThetaSecondMoment.lean,line 12](ThetaSecondMoment.lean#L12)

```lean
def thetaMajorant : ℝ
```

## `ThetaMacdonald.SecondMoment.macdonaldMajorant`

[ThetaSecondMoment.lean,line 13](ThetaSecondMoment.lean#L13)

```lean
def macdonaldMajorant : ℝ
```

## `ThetaMacdonald.SecondMoment.differenceMajorant`

[ThetaSecondMoment.lean,line 14](ThetaSecondMoment.lean#L14)

```lean
def differenceMajorant : ℝ
```

## `ThetaMacdonald.SecondMoment.thetaMajorant_nonneg`

[ThetaSecondMoment.lean,line 16](ThetaSecondMoment.lean#L16)

```lean
theorem thetaMajorant_nonneg : 0 ≤ thetaMajorant
```

## `ThetaMacdonald.SecondMoment.macdonaldMajorant_pos`

[ThetaSecondMoment.lean,line 20](ThetaSecondMoment.lean#L20)

```lean
theorem macdonaldMajorant_pos : 0 < macdonaldMajorant
```

## `ThetaMacdonald.SecondMoment.differenceMajorant_pos`

[ThetaSecondMoment.lean,line 23](ThetaSecondMoment.lean#L23)

```lean
theorem differenceMajorant_pos : 0 < differenceMajorant
```

## `ThetaMacdonald.SecondMoment.thetaDensity_bound`

[ThetaSecondMoment.lean,line 26](ThetaSecondMoment.lean#L26)

```lean
theorem thetaDensity_bound {u : ℝ} (hu : 0 ≤ u) :
    ‖thetaDensity u‖ ≤ thetaMajorant*Real.exp (-u)
```

## `ThetaMacdonald.SecondMoment.macdonaldDensity_bound`

[ThetaSecondMoment.lean,line 35](ThetaSecondMoment.lean#L35)

```lean
theorem macdonaldDensity_bound {u : ℝ} (hu : 0 ≤ u) :
    ‖macdonaldDensity u‖ ≤ macdonaldMajorant*Real.exp (-u)
```

## `ThetaMacdonald.SecondMoment.densityDifference_bound`

[ThetaSecondMoment.lean,line 55](ThetaSecondMoment.lean#L55)

```lean
theorem densityDifference_bound {u : ℝ} (hu : 0 ≤ u) :
    ‖densityDifference u‖ ≤ differenceMajorant*Real.exp (-u)
```

## `ThetaMacdonald.SecondMoment.integrable_theta_secondMoment`

[ThetaSecondMoment.lean,line 63](ThetaSecondMoment.lean#L63)

```lean
theorem integrable_theta_secondMoment :
    IntegrableOn (fun u : ℝ => u^2*thetaDensity u) (Ioi (0 : ℝ))
```

## `ThetaMacdonald.SecondMoment.integrable_macdonald_secondMoment`

[ThetaSecondMoment.lean,line 68](ThetaSecondMoment.lean#L68)

```lean
theorem integrable_macdonald_secondMoment :
    IntegrableOn (fun u : ℝ => u^2*macdonaldDensity u) (Ioi (0 : ℝ))
```

## `ThetaMacdonald.SecondMoment.integrable_difference_secondMoment`

[ThetaSecondMoment.lean,line 73](ThetaSecondMoment.lean#L73)

```lean
theorem integrable_difference_secondMoment :
    IntegrableOn (fun u : ℝ => u^2*densityDifference u) (Ioi (0 : ℝ))
```

## `ThetaMacdonald.SecondMoment.theta_secondMoment_tail`

[ThetaSecondMoment.lean,line 78](ThetaSecondMoment.lean#L78)

```lean
theorem theta_secondMoment_tail {u : ℝ} (hu : 0 ≤ u) :
    ‖∫ t in Ioi u, t^2*thetaDensity t‖ ≤
      16*thetaMajorant*Real.exp (-u/2)
```

## `ThetaMacdonald.SecondMoment.macdonald_secondMoment_tail`

[ThetaSecondMoment.lean,line 84](ThetaSecondMoment.lean#L84)

```lean
theorem macdonald_secondMoment_tail {u : ℝ} (hu : 0 ≤ u) :
    ‖∫ t in Ioi u, t^2*macdonaldDensity t‖ ≤
      16*macdonaldMajorant*Real.exp (-u/2)
```

## `ThetaMacdonald.SecondMoment.difference_secondMoment_tail`

[ThetaSecondMoment.lean,line 90](ThetaSecondMoment.lean#L90)

```lean
theorem difference_secondMoment_tail {u : ℝ} (hu : 0 ≤ u) :
    ‖∫ t in Ioi u, t^2*densityDifference t‖ ≤
      16*differenceMajorant*Real.exp (-u/2)
```

## `ThetaMacdonald.SecondMoment.cumulative_exponential_bound`

[ThetaSecondMoment.lean,line 96](ThetaSecondMoment.lean#L96)

```lean
theorem cumulative_exponential_bound {u : ℝ} (hu : 0 ≤ u) :
    ‖cumulative u‖ ≤ differenceMajorant*Real.exp (-u)
```

## `ThetaMacdonald.SecondMoment.cumulative_secondMoment_boundary`

[ThetaSecondMoment.lean,line 101](ThetaSecondMoment.lean#L101)

```lean
theorem cumulative_secondMoment_boundary :
    Tendsto (fun u : ℝ => u^2*cumulative u) atTop (𝓝 0)
```

## `ThetaMacdonald.SecondMoment.centered_weight_integrable`

[ThetaSecondMoment.lean,line 106](ThetaSecondMoment.lean#L106)

```lean
theorem centered_weight_integrable (c : ℝ) :
    IntegrableOn (fun u : ℝ => (u^2-c^2)*densityDifference u) (Ioi (0 : ℝ))
```

## `ThetaMacdonald.SecondMoment.actual_centered_secondMoment_pos`

[ThetaSecondMoment.lean,line 113](ThetaSecondMoment.lean#L113)

```lean
theorem actual_centered_secondMoment_pos :
    ∃ c : ℝ, 0 < c ∧
      0 < ∫ u in Ioi (0 : ℝ), (u^2-c^2)*densityDifference u
```

## `ThetaMacdonald.SecondMoment.actual_difference_secondMoment_pos`

[ThetaSecondMoment.lean,line 140](ThetaSecondMoment.lean#L140)

```lean
theorem actual_difference_secondMoment_pos :
    0 < ∫ u in Ioi (0 : ℝ), u^2*densityDifference u
```

## `ThetaMacdonald.SecondMoment.actual_secondMoment_order`

[ThetaSecondMoment.lean,line 156](ThetaSecondMoment.lean#L156)

```lean
theorem actual_secondMoment_order :
    (∫ u in Ioi (0 : ℝ), u^2*macdonaldDensity u) <
      ∫ u in Ioi (0 : ℝ), u^2*thetaDensity u
```

## `ThetaMacdonald.Mass.seedTail`

[ThetaSeedFTC.lean,line 12](ThetaSeedFTC.lean#L12)

```lean
def seedTail (u : ℝ) : ℝ
```

## `ThetaMacdonald.Mass.seedTailD1`

[ThetaSeedFTC.lean,line 13](ThetaSeedFTC.lean#L13)

```lean
def seedTailD1 (u : ℝ) : ℝ
```

## `ThetaMacdonald.Mass.seedTailD2`

[ThetaSeedFTC.lean,line 15](ThetaSeedFTC.lean#L15)

```lean
def seedTailD2 (u : ℝ) : ℝ
```

## `ThetaMacdonald.Mass.tailC`

[ThetaSeedFTC.lean,line 17](ThetaSeedFTC.lean#L17)

```lean
def tailC : ℝ
```

## `ThetaMacdonald.Mass.seedTail_eq_tsum`

[ThetaSeedFTC.lean,line 19](ThetaSeedFTC.lean#L19)

```lean
theorem seedTail_eq_tsum (u : ℝ) :
    seedTail u = ∑' k : ℕ, gaussianSeed (k+1) u
```

## `ThetaMacdonald.Mass.seedTailD1_eq_tsum`

[ThetaSeedFTC.lean,line 26](ThetaSeedFTC.lean#L26)

```lean
theorem seedTailD1_eq_tsum (u : ℝ) :
    seedTailD1 u = ∑' k : ℕ, gaussianSeedD1 (k+1) u
```

## `ThetaMacdonald.Mass.hasDerivAt_seedTail`

[ThetaSeedFTC.lean,line 35](ThetaSeedFTC.lean#L35)

```lean
theorem hasDerivAt_seedTail (u : ℝ) :
    HasDerivAt seedTail (seedTailD1 u) u
```

## `ThetaMacdonald.Mass.hasDerivAt_seedTailD1`

[ThetaSeedFTC.lean,line 42](ThetaSeedFTC.lean#L42)

```lean
theorem hasDerivAt_seedTailD1 (u : ℝ) :
    HasDerivAt seedTailD1 (seedTailD2 u) u
```

## `ThetaMacdonald.Mass.raw_eq_seedTail`

[ThetaSeedFTC.lean,line 49](ThetaSeedFTC.lean#L49)

```lean
theorem raw_eq_seedTail (u : ℝ) :
    thetaProfile u = 2*seedTailD2 u - (1/2 : ℝ)*seedTail u
```

## `ThetaMacdonald.Mass.seedTailD1_origin`

[ThetaSeedFTC.lean,line 56](ThetaSeedFTC.lean#L56)

```lean
theorem seedTailD1_origin : seedTailD1 0 = -(1/4 : ℝ)
```

## `ThetaMacdonald.Mass.seed_decay_data`

[ThetaSeedFTC.lean,line 65](ThetaSeedFTC.lean#L65)

```lean
theorem seed_decay_data {u : ℝ} (hu : 0 ≤ u) {k : ℕ} (hk : 1 ≤ k) :
    let z := zArg k u
    3 ≤ z ∧ u/2-z/2 ≤ -Real.pi*(k:ℝ)^2/4-u
```

## `ThetaMacdonald.Mass.seed_tail_bound`

[ThetaSeedFTC.lean,line 82](ThetaSeedFTC.lean#L82)

```lean
theorem seed_tail_bound {u : ℝ} (hu : 0 ≤ u) {k : ℕ} (hk : 1 ≤ k) :
    ‖gaussianSeed k u‖ ≤ thetaTailWeight k * Real.exp (-u)
```

## `ThetaMacdonald.Mass.seedD1_tail_bound`

[ThetaSeedFTC.lean,line 96](ThetaSeedFTC.lean#L96)

```lean
theorem seedD1_tail_bound {u : ℝ} (hu : 0 ≤ u) {k : ℕ} (hk : 1 ≤ k) :
    ‖gaussianSeedD1 k u‖ ≤ thetaTailWeight k * Real.exp (-u)
```

## `ThetaMacdonald.Mass.shifted_sum_bound`

[ThetaSeedFTC.lean,line 117](ThetaSeedFTC.lean#L117)

```lean
theorem shifted_sum_bound {f : ℕ → ℝ} (hf : Summable f) {u : ℝ}
    (hb : ∀ k : ℕ, ‖f (k+1)‖ ≤ thetaTailWeight (k+1)*Real.exp (-u)) :
    ‖∑' k : ℕ, f (k+1)‖ ≤ tailC*Real.exp (-u)
```

## `ThetaMacdonald.Mass.seedTail_bound`

[ThetaSeedFTC.lean,line 132](ThetaSeedFTC.lean#L132)

```lean
theorem seedTail_bound {u : ℝ} (hu : 0 ≤ u) :
    ‖seedTail u‖ ≤ tailC*Real.exp (-u)
```

## `ThetaMacdonald.Mass.seedTailD1_bound`

[ThetaSeedFTC.lean,line 138](ThetaSeedFTC.lean#L138)

```lean
theorem seedTailD1_bound {u : ℝ} (hu : 0 ≤ u) :
    ‖seedTailD1 u‖ ≤ tailC*Real.exp (-u)
```

## `ThetaMacdonald.Mass.integrable_seedTail`

[ThetaSeedFTC.lean,line 144](ThetaSeedFTC.lean#L144)

```lean
theorem integrable_seedTail : IntegrableOn seedTail (Ioi (0 : ℝ))
```

## `ThetaMacdonald.Mass.seedTailD1_tendsto_zero`

[ThetaSeedFTC.lean,line 151](ThetaSeedFTC.lean#L151)

```lean
theorem seedTailD1_tendsto_zero : Tendsto seedTailD1 atTop (𝓝 0)
```

## `ThetaMacdonald.Mass.integrable_seedTailD2`

[ThetaSeedFTC.lean,line 158](ThetaSeedFTC.lean#L158)

```lean
theorem integrable_seedTailD2 : IntegrableOn seedTailD2 (Ioi (0 : ℝ))
```

## `ThetaMacdonald.Mass.integral_seedTailD2`

[ThetaSeedFTC.lean,line 166](ThetaSeedFTC.lean#L166)

```lean
theorem integral_seedTailD2 :
    (∫ u in Ioi (0 : ℝ), seedTailD2 u) = (1/4 : ℝ)
```

## `ThetaMacdonald.Mass.thetaMass_improper_FTC`

[ThetaSeedFTC.lean,line 172](ThetaSeedFTC.lean#L172)

```lean
theorem thetaMass_improper_FTC :
    thetaMass = 1/2 - (1/2 : ℝ)*(∫ u in Ioi (0 : ℝ), seedTail u)
```

## `ThetaMacdonald.Series.gaussianMonomial`

[ThetaSeries.lean,line 24](ThetaSeries.lean#L24)

```lean
def gaussianMonomial (j k : ℕ) (u : ℝ) : ℝ
```

## `ThetaMacdonald.Series.gaussianMajorant`

[ThetaSeries.lean,line 28](ThetaSeries.lean#L28)

```lean
def gaussianMajorant (j : ℕ) (L U : ℝ) (k : ℕ) : ℝ
```

## `ThetaMacdonald.Series.zArg_nonneg`

[ThetaSeries.lean,line 32](ThetaSeries.lean#L32)

```lean
theorem zArg_nonneg (k : ℕ) (u : ℝ) : 0 ≤ zArg k u
```

## `ThetaMacdonald.Series.zArg_mono`

[ThetaSeries.lean,line 36](ThetaSeries.lean#L36)

```lean
theorem zArg_mono (k : ℕ) {u v : ℝ} (h : u ≤ v) :
    zArg k u ≤ zArg k v
```

## `ThetaMacdonald.Series.summable_gaussianMajorant`

[ThetaSeries.lean,line 43](ThetaSeries.lean#L43)

```lean
theorem summable_gaussianMajorant (j : ℕ) (L U : ℝ) :
    Summable (gaussianMajorant j L U)
```

## `ThetaMacdonald.Series.norm_gaussianMonomial_le`

[ThetaSeries.lean,line 49](ThetaSeries.lean#L49)

```lean
theorem norm_gaussianMonomial_le (j k : ℕ) {L U u : ℝ}
    (hu : u ∈ Icc L U) :
    ‖gaussianMonomial j k u‖ ≤ gaussianMajorant j L U k
```

## `ThetaMacdonald.Series.polynomialShell`

[ThetaSeries.lean,line 78](ThetaSeries.lean#L78)

```lean
def polynomialShell (s : Finset ℕ) (c : ℕ → ℝ) (k : ℕ) (u : ℝ) : ℝ
```

## `ThetaMacdonald.Series.polynomialMajorant`

[ThetaSeries.lean,line 81](ThetaSeries.lean#L81)

```lean
def polynomialMajorant (s : Finset ℕ) (c : ℕ → ℝ)
    (L U : ℝ) (k : ℕ) : ℝ
```

## `ThetaMacdonald.Series.summable_polynomialMajorant`

[ThetaSeries.lean,line 85](ThetaSeries.lean#L85)

```lean
theorem summable_polynomialMajorant (s : Finset ℕ) (c : ℕ → ℝ) (L U : ℝ) :
    Summable (polynomialMajorant s c L U)
```

## `ThetaMacdonald.Series.norm_polynomialShell_le`

[ThetaSeries.lean,line 103](ThetaSeries.lean#L103)

```lean
theorem norm_polynomialShell_le (s : Finset ℕ) (c : ℕ → ℝ) (k : ℕ)
    {L U u : ℝ} (hu : u ∈ Icc L U) :
    ‖polynomialShell s c k u‖ ≤ polynomialMajorant s c L U k
```

## `ThetaMacdonald.Series.shellCoefficient`

[ThetaSeries.lean,line 116](ThetaSeries.lean#L116)

```lean
def shellCoefficient : ℕ → ℕ → ℝ
  | 0, 1 => -12
  | 0, 2 => 8
  | 1, 1 => -30
  | 1, 2 => 60
  | 1, 3 => -16
  | 2, 1 => -75
  | 2, 2 => 330
  | 2, 3 => -224
  | 2, 4 => 32
  | _, _ => 0

def shellRow (r k : ℕ) (u : ℝ) : ℝ
```

## `ThetaMacdonald.Series.shellRow`

[ThetaSeries.lean,line 128](ThetaSeries.lean#L128)

```lean
def shellRow (r k : ℕ) (u : ℝ) : ℝ
```

## `ThetaMacdonald.Series.rowMajorant`

[ThetaSeries.lean,line 131](ThetaSeries.lean#L131)

```lean
def rowMajorant (r : ℕ) (L U : ℝ) (k : ℕ) : ℝ
```

## `ThetaMacdonald.Series.shellRow_zero`

[ThetaSeries.lean,line 134](ThetaSeries.lean#L134)

```lean
theorem shellRow_zero (k : ℕ) (u : ℝ) :
    shellRow 0 k u = rawShell k u
```

## `ThetaMacdonald.Series.shellRow_one`

[ThetaSeries.lean,line 140](ThetaSeries.lean#L140)

```lean
theorem shellRow_one (k : ℕ) (u : ℝ) :
    shellRow 1 k u = rawShellD1 k u
```

## `ThetaMacdonald.Series.shellRow_two`

[ThetaSeries.lean,line 146](ThetaSeries.lean#L146)

```lean
theorem shellRow_two (k : ℕ) (u : ℝ) :
    shellRow 2 k u = rawShellD2 k u
```

## `ThetaMacdonald.Series.summable_rowMajorant`

[ThetaSeries.lean,line 152](ThetaSeries.lean#L152)

```lean
theorem summable_rowMajorant (r : ℕ) (L U : ℝ) :
    Summable (rowMajorant r L U)
```

## `ThetaMacdonald.Series.norm_shellRow_le`

[ThetaSeries.lean,line 156](ThetaSeries.lean#L156)

```lean
theorem norm_shellRow_le (r k : ℕ) {L U u : ℝ} (hu : u ∈ Icc L U) :
    ‖shellRow r k u‖ ≤ rowMajorant r L U k
```

## `ThetaMacdonald.Series.summable_shellRow`

[ThetaSeries.lean,line 160](ThetaSeries.lean#L160)

```lean
theorem summable_shellRow (r : ℕ) (u : ℝ) :
    Summable (fun k => shellRow r k u)
```

## `ThetaMacdonald.Series.uniformlyOn_shellRow`

[ThetaSeries.lean,line 165](ThetaSeries.lean#L165)

```lean
theorem uniformlyOn_shellRow (r : ℕ) (L U : ℝ) :
    TendstoUniformlyOn
      (fun N u => ∑ k ∈ Finset.range N, shellRow r k u)
      (fun u => ∑' k, shellRow r k u) atTop (Icc L U)
```

## `ThetaMacdonald.Series.summable_rawShell`

[ThetaSeries.lean,line 172](ThetaSeries.lean#L172)

```lean
theorem summable_rawShell (u : ℝ) :
    Summable (fun k => rawShell k u)
```

## `ThetaMacdonald.Series.summable_rawShellD1`

[ThetaSeries.lean,line 176](ThetaSeries.lean#L176)

```lean
theorem summable_rawShellD1 (u : ℝ) :
    Summable (fun k => rawShellD1 k u)
```

## `ThetaMacdonald.Series.summable_rawShellD2`

[ThetaSeries.lean,line 180](ThetaSeries.lean#L180)

```lean
theorem summable_rawShellD2 (u : ℝ) :
    Summable (fun k => rawShellD2 k u)
```

## `ThetaMacdonald.Series.summable_norm_rawShell`

[ThetaSeries.lean,line 184](ThetaSeries.lean#L184)

```lean
theorem summable_norm_rawShell (u : ℝ) :
    Summable (fun k => ‖rawShell k u‖)
```

## `ThetaMacdonald.Series.summable_norm_rawShellD1`

[ThetaSeries.lean,line 188](ThetaSeries.lean#L188)

```lean
theorem summable_norm_rawShellD1 (u : ℝ) :
    Summable (fun k => ‖rawShellD1 k u‖)
```

## `ThetaMacdonald.Series.summable_norm_rawShellD2`

[ThetaSeries.lean,line 192](ThetaSeries.lean#L192)

```lean
theorem summable_norm_rawShellD2 (u : ℝ) :
    Summable (fun k => ‖rawShellD2 k u‖)
```

## `ThetaMacdonald.Series.uniformlyOn_rawShell`

[ThetaSeries.lean,line 196](ThetaSeries.lean#L196)

```lean
theorem uniformlyOn_rawShell (L U : ℝ) :
    TendstoUniformlyOn
      (fun N u => ∑ k ∈ Finset.range N, rawShell k u)
      (fun u => ∑' k, rawShell k u) atTop (Icc L U)
```

## `ThetaMacdonald.Series.uniformlyOn_rawShellD1`

[ThetaSeries.lean,line 202](ThetaSeries.lean#L202)

```lean
theorem uniformlyOn_rawShellD1 (L U : ℝ) :
    TendstoUniformlyOn
      (fun N u => ∑ k ∈ Finset.range N, rawShellD1 k u)
      (fun u => ∑' k, rawShellD1 k u) atTop (Icc L U)
```

## `ThetaMacdonald.Series.uniformlyOn_rawShellD2`

[ThetaSeries.lean,line 208](ThetaSeries.lean#L208)

```lean
theorem uniformlyOn_rawShellD2 (L U : ℝ) :
    TendstoUniformlyOn
      (fun N u => ∑ k ∈ Finset.range N, rawShellD2 k u)
      (fun u => ∑' k, rawShellD2 k u) atTop (Icc L U)
```

## `ThetaMacdonald.Series.hasDerivAt_tsum_rawShell_Ioo`

[ThetaSeries.lean,line 216](ThetaSeries.lean#L216)

```lean
theorem hasDerivAt_tsum_rawShell_Ioo {L U u : ℝ} (hu : u ∈ Ioo L U) :
    HasDerivAt (fun v => ∑' k, rawShell k v)
      (∑' k, rawShellD1 k u) u
```

## `ThetaMacdonald.Series.hasDerivAt_tsum_rawShellD1_Ioo`

[ThetaSeries.lean,line 226](ThetaSeries.lean#L226)

```lean
theorem hasDerivAt_tsum_rawShellD1_Ioo {L U u : ℝ} (hu : u ∈ Ioo L U) :
    HasDerivAt (fun v => ∑' k, rawShellD1 k v)
      (∑' k, rawShellD2 k u) u
```

## `ThetaMacdonald.Series.hasDerivAt_tsum_rawShell`

[ThetaSeries.lean,line 236](ThetaSeries.lean#L236)

```lean
theorem hasDerivAt_tsum_rawShell (u : ℝ) :
    HasDerivAt (fun v => ∑' k, rawShell k v)
      (∑' k, rawShellD1 k u) u
```

## `ThetaMacdonald.Series.hasDerivAt_tsum_rawShellD1`

[ThetaSeries.lean,line 242](ThetaSeries.lean#L242)

```lean
theorem hasDerivAt_tsum_rawShellD1 (u : ℝ) :
    HasDerivAt (fun v => ∑' k, rawShellD1 k v)
      (∑' k, rawShellD2 k u) u
```

## `ThetaMacdonald.Series.deriv_tsum_rawShell`

[ThetaSeries.lean,line 248](ThetaSeries.lean#L248)

```lean
theorem deriv_tsum_rawShell :
    deriv (fun v => ∑' k, rawShell k v) = fun v => ∑' k, rawShellD1 k v
```

## `ThetaMacdonald.Series.second_deriv_tsum_rawShell`

[ThetaSeries.lean,line 252](ThetaSeries.lean#L252)

```lean
theorem second_deriv_tsum_rawShell (u : ℝ) :
    deriv (deriv (fun v => ∑' k, rawShell k v)) u =
      ∑' k, rawShellD2 k u
```

## `ThetaMacdonald.Series.summable_rawShell_shifted`

[ThetaSeries.lean,line 258](ThetaSeries.lean#L258)

```lean
theorem summable_rawShell_shifted (u : ℝ) :
    Summable (fun n : ℕ => rawShell (n + 1) u)
```

## `ThetaMacdonald.Series.source_phi_summable`

[ThetaSeries.lean,line 263](ThetaSeries.lean#L263)

```lean
theorem source_phi_summable (u : ℝ) :
    Summable (fun n : ℕ =>
      (8 * Real.pi ^ 2 * ((n + 1 : ℕ) : ℝ) ^ 4 * Real.exp (9 * u / 2) -
        12 * Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (5 * u / 2)) *
      Real.exp (-Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * u)))
```

## `ThetaMacdonald.Series.rawShell_zero`

[ThetaSeries.lean,line 270](ThetaSeries.lean#L270)

```lean
theorem rawShell_zero (u : ℝ) : rawShell 0 u = 0
```

## `ThetaMacdonald.Series.tsum_rawShell_eq_shifted`

[ThetaSeries.lean,line 273](ThetaSeries.lean#L273)

```lean
theorem tsum_rawShell_eq_shifted (u : ℝ) :
    (∑' k : ℕ, rawShell k u) = ∑' n : ℕ, rawShell (n + 1) u
```

## `ThetaMacdonald.zArg`

[ThetaShellDerivative.lean,line 13](ThetaShellDerivative.lean#L13)

```lean
def zArg (k : ℕ) (u : ℝ) : ℝ
```

## `ThetaMacdonald.rawShell`

[ThetaShellDerivative.lean,line 15](ThetaShellDerivative.lean#L15)

```lean
def rawShell (k : ℕ) (u : ℝ) : ℝ
```

## `ThetaMacdonald.rawShellD1`

[ThetaShellDerivative.lean,line 18](ThetaShellDerivative.lean#L18)

```lean
def rawShellD1 (k : ℕ) (u : ℝ) : ℝ
```

## `ThetaMacdonald.rawShellD2`

[ThetaShellDerivative.lean,line 22](ThetaShellDerivative.lean#L22)

```lean
def rawShellD2 (k : ℕ) (u : ℝ) : ℝ
```

## `ThetaMacdonald.hasDerivAt_zArg`

[ThetaShellDerivative.lean,line 26](ThetaShellDerivative.lean#L26)

```lean
theorem hasDerivAt_zArg (k : ℕ) (u : ℝ) :
    HasDerivAt (zArg k) (2 * zArg k u) u
```

## `ThetaMacdonald.hasDerivAt_rawShell`

[ThetaShellDerivative.lean,line 35](ThetaShellDerivative.lean#L35)

```lean
theorem hasDerivAt_rawShell (k : ℕ) (u : ℝ) :
    HasDerivAt (rawShell k) (rawShellD1 k u) u
```

## `ThetaMacdonald.hasDerivAt_rawShellD1`

[ThetaShellDerivative.lean,line 45](ThetaShellDerivative.lean#L45)

```lean
theorem hasDerivAt_rawShellD1 (k : ℕ) (u : ℝ) :
    HasDerivAt (rawShellD1 k) (rawShellD2 k u) u
```

## `ThetaMacdonald.deriv_rawShell`

[ThetaShellDerivative.lean,line 56](ThetaShellDerivative.lean#L56)

```lean
theorem deriv_rawShell (k : ℕ) :
    deriv (rawShell k) = rawShellD1 k
```

## `ThetaMacdonald.deriv_rawShellD1`

[ThetaShellDerivative.lean,line 60](ThetaShellDerivative.lean#L60)

```lean
theorem deriv_rawShellD1 (k : ℕ) :
    deriv (rawShellD1 k) = rawShellD2 k
```

## `ThetaMacdonald.rawShell_eq_expanded`

[ThetaShellDerivative.lean,line 64](ThetaShellDerivative.lean#L64)

```lean
theorem rawShell_eq_expanded (k : ℕ) (u : ℝ) :
    rawShell k u =
      (8 * Real.pi^2 * (k : ℝ)^4 * Real.exp (9*u/2) -
        12 * Real.pi * (k : ℝ)^2 * Real.exp (5*u/2)) *
        Real.exp (-Real.pi * (k : ℝ)^2 * Real.exp (2*u))
```

## `ThetaMacdonald.shellZ`

[ThetaShellShape.lean,line 22](ThetaShellShape.lean#L22)

```lean
def shellZ (k : ℕ) (u : ℝ) : ℝ
```

## `ThetaMacdonald.shellT`

[ThetaShellShape.lean,line 25](ThetaShellShape.lean#L25)

```lean
def shellT (u : ℝ) : ℝ
```

## `ThetaMacdonald.shellW`

[ThetaShellShape.lean,line 27](ThetaShellShape.lean#L27)

```lean
def shellW (u : ℝ) : ℝ
```

## `ThetaMacdonald.logSlope`

[ThetaShellShape.lean,line 29](ThetaShellShape.lean#L29)

```lean
def logSlope (z t w : ℝ) : ℝ
```

## `ThetaMacdonald.slopeDerivative`

[ThetaShellShape.lean,line 32](ThetaShellShape.lean#L32)

```lean
def slopeDerivative (z t w : ℝ) : ℝ
```

## `ThetaMacdonald.shellT_pos`

[ThetaShellShape.lean,line 35](ThetaShellShape.lean#L35)

```lean
theorem shellT_pos (u : ℝ) : 0 < shellT u
```

## `ThetaMacdonald.shellW_pos`

[ThetaShellShape.lean,line 38](ThetaShellShape.lean#L38)

```lean
theorem shellW_pos (u : ℝ) : 0 < shellW u
```

## `ThetaMacdonald.shellT_ge_pi`

[ThetaShellShape.lean,line 41](ThetaShellShape.lean#L41)

```lean
theorem shellT_ge_pi {u : ℝ} (hu : 0 ≤ u) : Real.pi ≤ shellT u
```

## `ThetaMacdonald.shellT_le_shellZ_div_four`

[ThetaShellShape.lean,line 47](ThetaShellShape.lean#L47)

```lean
theorem shellT_le_shellZ_div_four {k : ℕ} (hk : 2 ≤ k) (u : ℝ) :
    shellT u ≤ shellZ k u / 4
```

## `ThetaMacdonald.shellW_le_shellT`

[ThetaShellShape.lean,line 56](ThetaShellShape.lean#L56)

```lean
theorem shellW_le_shellT {u : ℝ} (hu : 0 ≤ u) : shellW u ≤ shellT u
```

## `ThetaMacdonald.shellW_le_shellZ_div_four`

[ThetaShellShape.lean,line 61](ThetaShellShape.lean#L61)

```lean
theorem shellW_le_shellZ_div_four {k : ℕ} (hk : 2 ≤ k) {u : ℝ}
    (hu : 0 ≤ u) : shellW u ≤ shellZ k u / 4
```

## `ThetaMacdonald.shellZ_gt_twelve`

[ThetaShellShape.lean,line 65](ThetaShellShape.lean#L65)

```lean
theorem shellZ_gt_twelve {k : ℕ} (hk : 2 ≤ k) {u : ℝ} (hu : 0 ≤ u) :
    (12 : ℝ) < shellZ k u
```

## `ThetaMacdonald.shellT_mul_shellW`

[ThetaShellShape.lean,line 72](ThetaShellShape.lean#L72)

```lean
theorem shellT_mul_shellW (u : ℝ) : shellT u * shellW u = Real.pi ^ 2
```

## `ThetaMacdonald.shellW_eq_pi_sq_div_shellT`

[ThetaShellShape.lean,line 80](ThetaShellShape.lean#L80)

```lean
theorem shellW_eq_pi_sq_div_shellT (u : ℝ) :
    shellW u = Real.pi ^ 2 / shellT u
```

## `ThetaMacdonald.shellZ_one`

[ThetaShellShape.lean,line 85](ThetaShellShape.lean#L85)

```lean
theorem shellZ_one (u : ℝ) : shellZ 1 u = shellT u
```

## `ThetaMacdonald.logSlope_lt_of_ge_twelve`

[ThetaShellShape.lean,line 88](ThetaShellShape.lean#L88)

```lean
theorem logSlope_lt_of_ge_twelve {z t w : ℝ} (hz : 12 ≤ z)
    (ht : t ≤ z / 4) (hw : 0 ≤ w) :
    logSlope z t w < 5 - (3 / 2 : ℝ) * z
```

## `ThetaMacdonald.slopeDerivative_gt_of_ge_twelve`

[ThetaShellShape.lean,line 98](ThetaShellShape.lean#L98)

```lean
theorem slopeDerivative_gt_of_ge_twelve {z t w : ℝ} (hz : 12 ≤ z)
    (ht : 0 ≤ t) (hw : 0 ≤ w) :
    -5 * z < slopeDerivative z t w
```

## `ThetaMacdonald.curvature_factor_pos_of_ge_twelve`

[ThetaShellShape.lean,line 118](ThetaShellShape.lean#L118)

```lean
theorem curvature_factor_pos_of_ge_twelve {z t w : ℝ} (hz : 12 ≤ z)
    (ht0 : 0 ≤ t) (ht : t ≤ z / 4) (hw : 0 ≤ w) :
    0 < logSlope z t w ^ 2 + slopeDerivative z t w
```

## `ThetaMacdonald.higher_shell_logSlope_lt`

[ThetaShellShape.lean,line 132](ThetaShellShape.lean#L132)

```lean
theorem higher_shell_logSlope_lt {k : ℕ} (hk : 2 ≤ k) {u : ℝ} (hu : 0 ≤ u) :
    logSlope (shellZ k u) (shellT u) (shellW u) <
      5 - (3 / 2 : ℝ) * shellZ k u
```

## `ThetaMacdonald.higher_shell_logSlope_neg`

[ThetaShellShape.lean,line 138](ThetaShellShape.lean#L138)

```lean
theorem higher_shell_logSlope_neg {k : ℕ} (hk : 2 ≤ k) {u : ℝ} (hu : 0 ≤ u) :
    logSlope (shellZ k u) (shellT u) (shellW u) < 0
```

## `ThetaMacdonald.higher_shell_slopeDerivative_gt`

[ThetaShellShape.lean,line 144](ThetaShellShape.lean#L144)

```lean
theorem higher_shell_slopeDerivative_gt {k : ℕ} (hk : 2 ≤ k) {u : ℝ}
    (hu : 0 ≤ u) :
    -5 * shellZ k u < slopeDerivative (shellZ k u) (shellT u) (shellW u)
```

## `ThetaMacdonald.higher_shell_curvature_factor_pos`

[ThetaShellShape.lean,line 150](ThetaShellShape.lean#L150)

```lean
theorem higher_shell_curvature_factor_pos {k : ℕ} (hk : 2 ≤ k) {u : ℝ}
    (hu : 0 ≤ u) :
    0 < logSlope (shellZ k u) (shellT u) (shellW u) ^ 2 +
      slopeDerivative (shellZ k u) (shellT u) (shellW u)
```

## `ThetaMacdonald.first_slopeDerivative_pos_of_ge_pi`

[ThetaShellShape.lean,line 158](ThetaShellShape.lean#L158)

```lean
theorem first_slopeDerivative_pos_of_ge_pi {t : ℝ} (ht : Real.pi ≤ t) :
    0 < slopeDerivative t t (Real.pi ^ 2 / t)
```

## `ThetaMacdonald.first_shell_slopeDerivative_pos`

[ThetaShellShape.lean,line 178](ThetaShellShape.lean#L178)

```lean
theorem first_shell_slopeDerivative_pos {u : ℝ} (hu : 0 ≤ u) :
    0 < slopeDerivative (shellZ 1 u) (shellT u) (shellW u)
```

## `ThetaMacdonald.first_shell_curvature_factor_pos`

[ThetaShellShape.lean,line 183](ThetaShellShape.lean#L183)

```lean
theorem first_shell_curvature_factor_pos {u : ℝ} (hu : 0 ≤ u) :
    0 < logSlope (shellZ 1 u) (shellT u) (shellW u) ^ 2 +
      slopeDerivative (shellZ 1 u) (shellT u) (shellW u)
```

## `ThetaMacdonald.shell_curvature_factor_pos`

[ThetaShellShape.lean,line 189](ThetaShellShape.lean#L189)

```lean
theorem shell_curvature_factor_pos {k : ℕ} (hk : 1 ≤ k) {u : ℝ} (hu : 0 ≤ u) :
    0 < logSlope (shellZ k u) (shellT u) (shellW u) ^ 2 +
      slopeDerivative (shellZ k u) (shellT u) (shellW u)
```

## `ThetaMacdonald.Monotonicity.strictMonoOn_ratio`

[ThetaStrictIncrease.lean,line 13](ThetaStrictIncrease.lean#L13)

```lean
theorem strictMonoOn_ratio :
    StrictMonoOn Complete.ratio (Ici (0 : ℝ))
```
