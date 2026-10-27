# Exact paired-measure statements and conventions

All 101 package-owned public entries follow literally: 81 theorems,19 definitions and one abbreviation. Proof introductions and definition bodies are omitted except for the one-line domain alias. Full actual namespace names are used,not module labels: `SignedJensenPrep`, `SignedJensenKernelPrep`, `SignedJensenGaussianPrep`, `SignedJensenMeasurePrep`, `SignedJensenMomentsPrep` and `SignedJensenEntirePrep`. Repeated local names such as `momentCoefficient` are distinguished by namespace. [Source/import map](SOURCE-HANDOFF.md), [report coverage](evidence/public-declarations.json).

The actual domain is `SignedJensenMeasurePrep.U := {u : ℝ // 0 ≤ u}`,with its inherited Borel measurable structure,including zero. Inputs are two positive `Measure U` values. The main measure/entire/error results require `b>0` and genuine `Integrable (gaussian b) (μp + μm)`,where `gaussian b u = exp(b*u²)`. No probability,equal-mass,nonzero,mutual-singularity or separate sigma-finite instance is assumed. The sum measure is not identified with Jordan/total variation,and a finite-looking totalized integral is not a replacement for Integrable. Helper signatures retain their own weaker or different displayed hypotheses.

The kernel is `completeKernel a = ∑' j, (-a)^j/(2*j)!`; its native argument is `z*(u:ℂ)^2`. `signedPair` is the explicit difference of two complex integrals. Real signed moments are the difference of the two integrals of `u^(2*j)`. The infinite coefficient is `SignedJensenEntirePrep.momentCoefficient μp μm j = (-1)^j*(signedMoment μp μm j:ℂ)/(2*j)!`. The separate `SignedJensenMomentsPrep.momentCoefficient d z j` is an auxiliary finite-linearity coefficient,not the same declaration.

`weight d j` is the finite falling product for `j≤d`,zero above d;the finite polynomial uses the inclusive range `0..d`. Its dictionary is proved for every natural degree,including zero. The approximation theorem requires `d≥1`,`r≥0`,`‖z‖≤r` and the genuine sum-measure Gaussian premise. Its exact bound is `((r²/(3*b²*d))*exp(r/(2*b)))*M_b`,where `M_b = ∫ gaussian b d(μp+μm)`. There is no extra factor two. The pointwise precursor retains `1/24`;the Gaussian integrated theorem retains `1/3`.

The infinite moment `HasSum`/dictionary and genuine integral-norm summability justify interchange before transferring differentiability and analyticity to the actual paired integral. They retain the Gaussian premise;it is not proved for an arithmetic or theta density here. The README's cosine/square-root explanation and disk supremum display are classical consequences,not extra exported Lean theorems. No sharpness or zero-location conclusion is included.

## `SignedJensenMomentsPrep.evenPower`

[JensenEvenMoments.lean,line 30](JensenEvenMoments.lean#L30)

```lean
def evenPower (j : ℕ) (u : U) : ℝ
```

## `SignedJensenMomentsPrep.evenPower_nonneg`

[JensenEvenMoments.lean,line 32](JensenEvenMoments.lean#L32)

```lean
theorem evenPower_nonneg (j : ℕ) (u : U) : 0 ≤ evenPower j u
```

## `SignedJensenMomentsPrep.evenPower_le_gaussian`

[JensenEvenMoments.lean,line 37](JensenEvenMoments.lean#L37)

```lean
theorem evenPower_le_gaussian (b : ℝ) (j : ℕ) (hb : 0 < b) (u : U) :
    evenPower j u ≤ ((j.factorial : ℝ) / b ^ j) * gaussian b u
```

## `SignedJensenMomentsPrep.integrable_evenPower`

[JensenEvenMoments.lean,line 60](JensenEvenMoments.lean#L60)

```lean
theorem integrable_evenPower (μ : Measure U) (b : ℝ) (j : ℕ)
    (hb : 0 < b) (hG : Integrable (gaussian b) μ) :
    Integrable (evenPower j) μ
```

## `SignedJensenMomentsPrep.integral_evenPower_nonneg`

[JensenEvenMoments.lean,line 71](JensenEvenMoments.lean#L71)

```lean
theorem integral_evenPower_nonneg (μ : Measure U) (j : ℕ) :
    0 ≤ ∫ u, evenPower j u ∂μ
```

## `SignedJensenMomentsPrep.integral_evenPower_le`

[JensenEvenMoments.lean,line 77](JensenEvenMoments.lean#L77)

```lean
theorem integral_evenPower_le (μ : Measure U) (b : ℝ) (j : ℕ)
    (hb : 0 < b) (hG : Integrable (gaussian b) μ) :
    (∫ u, evenPower j u ∂μ) ≤
      ((j.factorial : ℝ) / b ^ j) * (∫ u, gaussian b u ∂μ)
```

## `SignedJensenMomentsPrep.signedMoment`

[JensenEvenMoments.lean,line 120](JensenEvenMoments.lean#L120)

```lean
def signedMoment (μp μm : Measure U) (j : ℕ) : ℝ
```

## `SignedJensenMomentsPrep.finiteMomentPolynomial`

[JensenEvenMoments.lean,line 125](JensenEvenMoments.lean#L125)

```lean
def finiteMomentPolynomial (μp μm : Measure U) (d : ℕ) (z : ℂ) : ℂ
```

## `SignedJensenMomentsPrep.momentCoefficient`

[JensenEvenMoments.lean,line 132](JensenEvenMoments.lean#L132)

```lean
def momentCoefficient (d : ℕ) (z : ℂ) (j : ℕ) : ℂ
```

## `SignedJensenMomentsPrep.integrable_complex_evenPower`

[JensenEvenMoments.lean,line 136](JensenEvenMoments.lean#L136)

```lean
theorem integrable_complex_evenPower (μ : Measure U) (b : ℝ) (j : ℕ)
    (hb : 0 < b) (hG : Integrable (gaussian b) μ) :
    Integrable (fun u => (evenPower j u : ℂ)) μ
```

## `SignedJensenMomentsPrep.weighted_kernelTerm_eq`

[JensenEvenMoments.lean,line 143](JensenEvenMoments.lean#L143)

```lean
theorem weighted_kernelTerm_eq (d : ℕ) (z : ℂ) (j : ℕ) (u : U) :
    (SignedJensenPrep.weight d j : ℂ) *
        SignedJensenKernelPrep.kernelTerm (z * (u : ℂ) ^ 2) j =
      momentCoefficient d z j * (evenPower j u : ℂ)
```

## `SignedJensenMomentsPrep.finiteNativeKernel_expansion`

[JensenEvenMoments.lean,line 151](JensenEvenMoments.lean#L151)

```lean
theorem finiteNativeKernel_expansion (d : ℕ) (z : ℂ) (u : U) :
    finiteNativeKernel d z u =
      ∑ j ∈ Finset.range (d + 1),
        momentCoefficient d z j * (evenPower j u : ℂ)
```

## `SignedJensenMomentsPrep.integrable_finiteNativeKernel_all_degrees`

[JensenEvenMoments.lean,line 162](JensenEvenMoments.lean#L162)

```lean
theorem integrable_finiteNativeKernel_all_degrees (μ : Measure U)
    (b : ℝ) (d : ℕ) (z : ℂ) (hb : 0 < b)
    (hG : Integrable (gaussian b) μ) :
    Integrable (finiteNativeKernel d z) μ
```

## `SignedJensenMomentsPrep.integral_finiteNativeKernel`

[JensenEvenMoments.lean,line 178](JensenEvenMoments.lean#L178)

```lean
theorem integral_finiteNativeKernel (μ : Measure U) (b : ℝ) (d : ℕ)
    (z : ℂ) (hb : 0 < b) (hG : Integrable (gaussian b) μ) :
    (∫ u, finiteNativeKernel d z u ∂μ) =
      ∑ j ∈ Finset.range (d + 1),
        momentCoefficient d z j * ((∫ u, evenPower j u ∂μ) : ℂ)
```

## `SignedJensenMomentsPrep.signedPair_finiteNativeKernel_eq`

[JensenEvenMoments.lean,line 194](JensenEvenMoments.lean#L194)

```lean
theorem signedPair_finiteNativeKernel_eq (μp μm : Measure U) (b : ℝ)
    (d : ℕ) (z : ℂ) (hb : 0 < b)
    (hG : Integrable (gaussian b) (μp + μm)) :
    signedPair μp μm (finiteNativeKernel d z) =
      finiteMomentPolynomial μp μm d z
```

## `SignedJensenMomentsPrep.finiteMomentPolynomial_error`

[JensenEvenMoments.lean,line 211](JensenEvenMoments.lean#L211)

```lean
theorem finiteMomentPolynomial_error (μp μm : Measure U) (b r : ℝ)
    (z : ℂ) (d : ℕ) (hb : 0 < b) (hr : 0 ≤ r) (hz : ‖z‖ ≤ r)
    (hd : 1 ≤ d) (hG : Integrable (gaussian b) (μp + μm)) :
    ‖finiteMomentPolynomial μp μm d z - signedPair μp μm (nativeKernel z)‖ ≤
      (r ^ 2 / (24 * (d : ℝ))) * (∫ u, fourthCosh r u ∂(μp + μm))
```

## `SignedJensenMomentsPrep.finiteMomentPolynomial_error_gaussian`

[JensenEvenMoments.lean,line 222](JensenEvenMoments.lean#L222)

```lean
theorem finiteMomentPolynomial_error_gaussian (μp μm : Measure U)
    (b r : ℝ) (z : ℂ) (d : ℕ) (hb : 0 < b) (hr : 0 ≤ r)
    (hz : ‖z‖ ≤ r) (hd : 1 ≤ d)
    (hG : Integrable (gaussian b) (μp + μm)) :
    ‖finiteMomentPolynomial μp μm d z - signedPair μp μm (nativeKernel z)‖ ≤
      ((r ^ 2 / (3 * b ^ 2 * (d : ℝ))) * Real.exp (r / (2 * b))) *
        (∫ u, gaussian b u ∂(μp + μm))
```

## `SignedJensenGaussianPrep.cosh_le_exp_nonneg`

[JensenGaussianMeasure.lean,line 35](JensenGaussianMeasure.lean#L35)

```lean
theorem cosh_le_exp_nonneg {x : ℝ} (hx : 0 ≤ x) :
    Real.cosh x ≤ Real.exp x
```

## `SignedJensenGaussianPrep.sqrt_mul_le_gaussian_split`

[JensenGaussianMeasure.lean,line 44](JensenGaussianMeasure.lean#L44)

```lean
theorem sqrt_mul_le_gaussian_split {b r u : ℝ}
    (hb : 0 < b) (hr : 0 ≤ r) :
    Real.sqrt r * u ≤ r / (2 * b) + b * u ^ 2 / 2
```

## `SignedJensenGaussianPrep.cosh_gaussian_half`

[JensenGaussianMeasure.lean,line 59](JensenGaussianMeasure.lean#L59)

```lean
theorem cosh_gaussian_half {b r u : ℝ}
    (hb : 0 < b) (hr : 0 ≤ r) (hu : 0 ≤ u) :
    Real.cosh (Real.sqrt r * u) ≤
      Real.exp (r / (2 * b)) * Real.exp (b * u ^ 2 / 2)
```

## `SignedJensenGaussianPrep.fourth_gaussian_half`

[JensenGaussianMeasure.lean,line 73](JensenGaussianMeasure.lean#L73)

```lean
theorem fourth_gaussian_half {b : ℝ} (hb : 0 < b) (u : ℝ) :
    u ^ 4 ≤ (8 / b ^ 2) * Real.exp (b * u ^ 2 / 2)
```

## `SignedJensenGaussianPrep.fourth_cosh_gaussian`

[JensenGaussianMeasure.lean,line 88](JensenGaussianMeasure.lean#L88)

```lean
theorem fourth_cosh_gaussian {b r u : ℝ}
    (hb : 0 < b) (hr : 0 ≤ r) (hu : 0 ≤ u) :
    u ^ 4 * Real.cosh (Real.sqrt r * u) ≤
      ((8 / b ^ 2) * Real.exp (r / (2 * b))) * Real.exp (b * u ^ 2)
```

## `SignedJensenGaussianPrep.cosh_gaussian_full`

[JensenGaussianMeasure.lean,line 111](JensenGaussianMeasure.lean#L111)

```lean
theorem cosh_gaussian_full {b r u : ℝ}
    (hb : 0 < b) (hr : 0 ≤ r) (hu : 0 ≤ u) :
    Real.cosh (Real.sqrt r * u) ≤
      Real.exp (r / (4 * b)) * Real.exp (b * u ^ 2)
```

## `SignedJensenGaussianPrep.pointwise_error_gaussian`

[JensenGaussianMeasure.lean,line 123](JensenGaussianMeasure.lean#L123)

```lean
theorem pointwise_error_gaussian {b d r u : ℝ}
    (hb : 0 < b) (hd : 0 < d) (hr : 0 ≤ r) (hu : 0 ≤ u) :
    (r ^ 2 * u ^ 4 / (24 * d)) * Real.cosh (Real.sqrt r * u) ≤
      ((r ^ 2 / (3 * b ^ 2 * d)) * Real.exp (r / (2 * b))) *
        Real.exp (b * u ^ 2)
```

## `SignedJensenMeasurePrep.U`

[JensenGaussianMeasure.lean,line 161](JensenGaussianMeasure.lean#L161)

```lean
abbrev U := {u : ℝ // 0 ≤ u}
```

## `SignedJensenMeasurePrep.gaussian`

[JensenGaussianMeasure.lean,line 163](JensenGaussianMeasure.lean#L163)

```lean
def gaussian (b : ℝ) (u : U) : ℝ
```

## `SignedJensenMeasurePrep.nativeKernel`

[JensenGaussianMeasure.lean,line 165](JensenGaussianMeasure.lean#L165)

```lean
def nativeKernel (z : ℂ) (u : U) : ℂ
```

## `SignedJensenMeasurePrep.finiteNativeKernel`

[JensenGaussianMeasure.lean,line 168](JensenGaussianMeasure.lean#L168)

```lean
def finiteNativeKernel (d : ℕ) (z : ℂ) (u : U) : ℂ
```

## `SignedJensenMeasurePrep.fourthCosh`

[JensenGaussianMeasure.lean,line 171](JensenGaussianMeasure.lean#L171)

```lean
def fourthCosh (r : ℝ) (u : U) : ℝ
```

## `SignedJensenMeasurePrep.signedPair`

[JensenGaussianMeasure.lean,line 174](JensenGaussianMeasure.lean#L174)

```lean
def signedPair (μp μm : Measure U) (f : U → ℂ) : ℂ
```

## `SignedJensenMeasurePrep.gaussian_mass_nonneg`

[JensenGaussianMeasure.lean,line 178](JensenGaussianMeasure.lean#L178)

```lean
theorem gaussian_mass_nonneg (μ : Measure U) (b : ℝ) :
    0 ≤ ∫ u, gaussian b u ∂μ
```

## `SignedJensenMeasurePrep.measurable_kernelTerm`

[JensenGaussianMeasure.lean,line 181](JensenGaussianMeasure.lean#L181)

```lean
theorem measurable_kernelTerm (z : ℂ) (j : ℕ) :
    Measurable (fun u : U =>
      SignedJensenKernelPrep.kernelTerm (z * (u : ℂ) ^ 2) j)
```

## `SignedJensenMeasurePrep.stronglyMeasurable_nativeKernel`

[JensenGaussianMeasure.lean,line 189](JensenGaussianMeasure.lean#L189)

```lean
theorem stronglyMeasurable_nativeKernel (z : ℂ) :
    StronglyMeasurable (nativeKernel z)
```

## `SignedJensenMeasurePrep.measurable_nativeKernel`

[JensenGaussianMeasure.lean,line 206](JensenGaussianMeasure.lean#L206)

```lean
theorem measurable_nativeKernel (z : ℂ) : Measurable (nativeKernel z)
```

## `SignedJensenMeasurePrep.stronglyMeasurable_finiteNativeKernel`

[JensenGaussianMeasure.lean,line 209](JensenGaussianMeasure.lean#L209)

```lean
theorem stronglyMeasurable_finiteNativeKernel (d : ℕ) (z : ℂ) :
    StronglyMeasurable (finiteNativeKernel d z)
```

## `SignedJensenMeasurePrep.measurable_finiteNativeKernel`

[JensenGaussianMeasure.lean,line 216](JensenGaussianMeasure.lean#L216)

```lean
theorem measurable_finiteNativeKernel (d : ℕ) (z : ℂ) :
    Measurable (finiteNativeKernel d z)
```

## `SignedJensenMeasurePrep.nativeKernel_norm_le`

[JensenGaussianMeasure.lean,line 220](JensenGaussianMeasure.lean#L220)

```lean
theorem nativeKernel_norm_le (z : ℂ) (r : ℝ)
    (hr : 0 ≤ r) (hz : ‖z‖ ≤ r) (u : U) :
    ‖nativeKernel z u‖ ≤ Real.cosh (Real.sqrt r * (u : ℝ))
```

## `SignedJensenMeasurePrep.integrable_nativeKernel`

[JensenGaussianMeasure.lean,line 234](JensenGaussianMeasure.lean#L234)

```lean
theorem integrable_nativeKernel (μ : Measure U) (b r : ℝ) (z : ℂ)
    (hb : 0 < b) (hr : 0 ≤ r) (hz : ‖z‖ ≤ r)
    (hG : Integrable (gaussian b) μ) : Integrable (nativeKernel z) μ
```

## `SignedJensenMeasurePrep.integrable_fourthCosh`

[JensenGaussianMeasure.lean,line 243](JensenGaussianMeasure.lean#L243)

```lean
theorem integrable_fourthCosh (μ : Measure U) (b r : ℝ)
    (hb : 0 < b) (hr : 0 ≤ r)
    (hG : Integrable (gaussian b) μ) : Integrable (fourthCosh r) μ
```

## `SignedJensenMeasurePrep.integrable_kernelError`

[JensenGaussianMeasure.lean,line 255](JensenGaussianMeasure.lean#L255)

```lean
theorem integrable_kernelError (μ : Measure U) (b r : ℝ) (z : ℂ) (d : ℕ)
    (hb : 0 < b) (hr : 0 ≤ r) (hz : ‖z‖ ≤ r) (hd : 1 ≤ d)
    (hG : Integrable (gaussian b) μ) :
    Integrable (fun u => finiteNativeKernel d z u - nativeKernel z u) μ
```

## `SignedJensenMeasurePrep.integrable_finiteNativeKernel`

[JensenGaussianMeasure.lean,line 270](JensenGaussianMeasure.lean#L270)

```lean
theorem integrable_finiteNativeKernel (μ : Measure U) (b r : ℝ) (z : ℂ) (d : ℕ)
    (hb : 0 < b) (hr : 0 ≤ r) (hz : ‖z‖ ≤ r) (hd : 1 ≤ d)
    (hG : Integrable (gaussian b) μ) : Integrable (finiteNativeKernel d z) μ
```

## `SignedJensenMeasurePrep.signedPair_difference_bound`

[JensenGaussianMeasure.lean,line 282](JensenGaussianMeasure.lean#L282)

```lean
theorem signedPair_difference_bound (μp μm : Measure U)
    (f g : U → ℂ) (a : U → ℝ)
    (hf : Integrable f (μp + μm)) (hg : Integrable g (μp + μm))
    (ha : Integrable a (μp + μm)) (hbound : ∀ u, ‖f u - g u‖ ≤ a u) :
    ‖signedPair μp μm f - signedPair μp μm g‖ ≤ ∫ u, a u ∂(μp + μm)
```

## `SignedJensenMeasurePrep.signedPair_kernel_error`

[JensenGaussianMeasure.lean,line 308](JensenGaussianMeasure.lean#L308)

```lean
theorem signedPair_kernel_error (μp μm : Measure U) (b r : ℝ) (z : ℂ) (d : ℕ)
    (hb : 0 < b) (hr : 0 ≤ r) (hz : ‖z‖ ≤ r) (hd : 1 ≤ d)
    (hG : Integrable (gaussian b) (μp + μm)) :
    ‖signedPair μp μm (finiteNativeKernel d z) - signedPair μp μm (nativeKernel z)‖ ≤
      (r ^ 2 / (24 * (d : ℝ))) * (∫ u, fourthCosh r u ∂(μp + μm))
```

## `SignedJensenMeasurePrep.signedPair_kernel_error_gaussian`

[JensenGaussianMeasure.lean,line 328](JensenGaussianMeasure.lean#L328)

```lean
theorem signedPair_kernel_error_gaussian (μp μm : Measure U)
    (b r : ℝ) (z : ℂ) (d : ℕ)
    (hb : 0 < b) (hr : 0 ≤ r) (hz : ‖z‖ ≤ r) (hd : 1 ≤ d)
    (hG : Integrable (gaussian b) (μp + μm)) :
    ‖signedPair μp μm (finiteNativeKernel d z) - signedPair μp μm (nativeKernel z)‖ ≤
      ((r ^ 2 / (3 * b ^ 2 * (d : ℝ))) * Real.exp (r / (2 * b))) *
        (∫ u, gaussian b u ∂(μp + μm))
```

## `SignedJensenEntirePrep.seriesTerm`

[JensenMomentEntire.lean,line 30](JensenMomentEntire.lean#L30)

```lean
def seriesTerm (z : ℂ) (u : U) (j : ℕ) : ℂ
```

## `SignedJensenEntirePrep.momentCoefficient`

[JensenMomentEntire.lean,line 33](JensenMomentEntire.lean#L33)

```lean
def momentCoefficient (μp μm : Measure U) (j : ℕ) : ℂ
```

## `SignedJensenEntirePrep.momentTransform`

[JensenMomentEntire.lean,line 36](JensenMomentEntire.lean#L36)

```lean
def momentTransform (μp μm : Measure U) (z : ℂ) : ℂ
```

## `SignedJensenEntirePrep.majorant`

[JensenMomentEntire.lean,line 40](JensenMomentEntire.lean#L40)

```lean
def majorant (b r : ℝ) (j : ℕ) : ℝ
```

## `SignedJensenEntirePrep.factorial_square_le`

[JensenMomentEntire.lean,line 43](JensenMomentEntire.lean#L43)

```lean
theorem factorial_square_le (j : ℕ) :
    (j.factorial : ℝ) * (j.factorial : ℝ) ≤ ((2 * j).factorial : ℝ)
```

## `SignedJensenEntirePrep.factorial_ratio_le`

[JensenMomentEntire.lean,line 51](JensenMomentEntire.lean#L51)

```lean
theorem factorial_ratio_le (j : ℕ) :
    (j.factorial : ℝ) / ((2 * j).factorial : ℝ) ≤ 1 / (j.factorial : ℝ)
```

## `SignedJensenEntirePrep.majorant_nonneg`

[JensenMomentEntire.lean,line 58](JensenMomentEntire.lean#L58)

```lean
theorem majorant_nonneg (b r : ℝ) (j : ℕ) (hb : 0 < b) (hr : 0 ≤ r) :
    0 ≤ majorant b r j
```

## `SignedJensenEntirePrep.majorant_hasSum`

[JensenMomentEntire.lean,line 64](JensenMomentEntire.lean#L64)

```lean
theorem majorant_hasSum (b r : ℝ) :
    HasSum (majorant b r) (Real.exp (r / b))
```

## `SignedJensenEntirePrep.seriesTerm_eq`

[JensenMomentEntire.lean,line 70](JensenMomentEntire.lean#L70)

```lean
theorem seriesTerm_eq (z : ℂ) (u : U) (j : ℕ) :
    seriesTerm z u j =
      ((-1 : ℂ) ^ j * z ^ j / ((2 * j).factorial : ℂ)) *
        (evenPower j u : ℂ)
```

## `SignedJensenEntirePrep.seriesTerm_norm`

[JensenMomentEntire.lean,line 78](JensenMomentEntire.lean#L78)

```lean
theorem seriesTerm_norm (z : ℂ) (u : U) (j : ℕ) :
    ‖seriesTerm z u j‖ =
      (‖z‖ ^ j / ((2 * j).factorial : ℝ)) * evenPower j u
```

## `SignedJensenEntirePrep.seriesTerm_norm_le`

[JensenMomentEntire.lean,line 87](JensenMomentEntire.lean#L87)

```lean
theorem seriesTerm_norm_le (z : ℂ) (u : U) (j : ℕ) (b r : ℝ)
    (hb : 0 < b) (hr : 0 ≤ r) (hz : ‖z‖ ≤ r) :
    ‖seriesTerm z u j‖ ≤ majorant b r j * gaussian b u
```

## `SignedJensenEntirePrep.integrable_seriesTerm`

[JensenMomentEntire.lean,line 117](JensenMomentEntire.lean#L117)

```lean
theorem integrable_seriesTerm (μ : Measure U) (b : ℝ) (z : ℂ) (j : ℕ)
    (hb : 0 < b) (hG : Integrable (gaussian b) μ) :
    Integrable (fun u => seriesTerm z u j) μ
```

## `SignedJensenEntirePrep.integral_norm_seriesTerm_le`

[JensenMomentEntire.lean,line 123](JensenMomentEntire.lean#L123)

```lean
theorem integral_norm_seriesTerm_le (μ : Measure U) (b r : ℝ) (z : ℂ)
    (j : ℕ) (hb : 0 < b) (hr : 0 ≤ r) (hz : ‖z‖ ≤ r)
    (hG : Integrable (gaussian b) μ) :
    (∫ u, ‖seriesTerm z u j‖ ∂μ) ≤
      (∫ u, gaussian b u ∂μ) * majorant b r j
```

## `SignedJensenEntirePrep.summable_integral_norm_seriesTerm`

[JensenMomentEntire.lean,line 137](JensenMomentEntire.lean#L137)

```lean
theorem summable_integral_norm_seriesTerm (μ : Measure U) (b r : ℝ) (z : ℂ)
    (hb : 0 < b) (hr : 0 ≤ r) (hz : ‖z‖ ≤ r)
    (hG : Integrable (gaussian b) μ) :
    Summable (fun j => ∫ u, ‖seriesTerm z u j‖ ∂μ)
```

## `SignedJensenEntirePrep.tsum_integral_norm_seriesTerm_le`

[JensenMomentEntire.lean,line 147](JensenMomentEntire.lean#L147)

```lean
theorem tsum_integral_norm_seriesTerm_le (μ : Measure U) (b r : ℝ) (z : ℂ)
    (hb : 0 < b) (hr : 0 ≤ r) (hz : ‖z‖ ≤ r)
    (hG : Integrable (gaussian b) μ) :
    (∑' j, ∫ u, ‖seriesTerm z u j‖ ∂μ) ≤
      (∫ u, gaussian b u ∂μ) * Real.exp (r / b)
```

## `SignedJensenEntirePrep.integral_seriesTerm`

[JensenMomentEntire.lean,line 157](JensenMomentEntire.lean#L157)

```lean
theorem integral_seriesTerm (μ : Measure U) (b : ℝ) (z : ℂ) (j : ℕ)
    (hb : 0 < b) (hG : Integrable (gaussian b) μ) :
    (∫ u, seriesTerm z u j ∂μ) =
      ((-1 : ℂ) ^ j * z ^ j / ((2 * j).factorial : ℂ)) *
        ((∫ u, evenPower j u ∂μ) : ℂ)
```

## `SignedJensenEntirePrep.integral_nativeKernel_hasSum`

[JensenMomentEntire.lean,line 167](JensenMomentEntire.lean#L167)

```lean
theorem integral_nativeKernel_hasSum (μ : Measure U) (b : ℝ) (z : ℂ)
    (hb : 0 < b) (hG : Integrable (gaussian b) μ) :
    HasSum (fun j => ∫ u, seriesTerm z u j ∂μ)
      (∫ u, nativeKernel z u ∂μ)
```

## `SignedJensenEntirePrep.integral_seriesTerm_difference`

[JensenMomentEntire.lean,line 175](JensenMomentEntire.lean#L175)

```lean
theorem integral_seriesTerm_difference (μp μm : Measure U) (b : ℝ)
    (z : ℂ) (j : ℕ) (hb : 0 < b)
    (hG : Integrable (gaussian b) (μp + μm)) :
    (∫ u, seriesTerm z u j ∂μp) - (∫ u, seriesTerm z u j ∂μm) =
      momentCoefficient μp μm j * z ^ j
```

## `SignedJensenEntirePrep.norm_momentTerm_le`

[JensenMomentEntire.lean,line 185](JensenMomentEntire.lean#L185)

```lean
theorem norm_momentTerm_le (μp μm : Measure U) (b : ℝ) (z : ℂ) (j : ℕ)
    (hb : 0 < b) (hG : Integrable (gaussian b) (μp + μm)) :
    ‖momentCoefficient μp μm j * z ^ j‖ ≤
      ∫ u, ‖seriesTerm z u j‖ ∂(μp + μm)
```

## `SignedJensenEntirePrep.summable_coefficient_norm_radius`

[JensenMomentEntire.lean,line 203](JensenMomentEntire.lean#L203)

```lean
theorem summable_coefficient_norm_radius (μp μm : Measure U) (b r : ℝ)
    (hb : 0 < b) (hr : 0 ≤ r)
    (hG : Integrable (gaussian b) (μp + μm)) :
    Summable (fun j => ‖momentCoefficient μp μm j‖ * r ^ j)
```

## `SignedJensenEntirePrep.signedPair_nativeKernel_hasSum`

[JensenMomentEntire.lean,line 215](JensenMomentEntire.lean#L215)

```lean
theorem signedPair_nativeKernel_hasSum (μp μm : Measure U) (b : ℝ) (z : ℂ)
    (hb : 0 < b) (hG : Integrable (gaussian b) (μp + μm)) :
    HasSum (fun j => momentCoefficient μp μm j * z ^ j)
      (signedPair μp μm (nativeKernel z))
```

## `SignedJensenEntirePrep.signedPair_nativeKernel_eq`

[JensenMomentEntire.lean,line 226](JensenMomentEntire.lean#L226)

```lean
theorem signedPair_nativeKernel_eq (μp μm : Measure U) (b : ℝ) (z : ℂ)
    (hb : 0 < b) (hG : Integrable (gaussian b) (μp + μm)) :
    signedPair μp μm (nativeKernel z) = momentTransform μp μm z
```

## `SignedJensenEntirePrep.differentiable_momentTransform`

[JensenMomentEntire.lean,line 269](JensenMomentEntire.lean#L269)

```lean
theorem differentiable_momentTransform (μp μm : Measure U) (b : ℝ)
    (hb : 0 < b) (hG : Integrable (gaussian b) (μp + μm)) :
    Differentiable ℂ (momentTransform μp μm)
```

## `SignedJensenEntirePrep.analyticAt_momentTransform`

[JensenMomentEntire.lean,line 303](JensenMomentEntire.lean#L303)

```lean
theorem analyticAt_momentTransform (μp μm : Measure U) (b : ℝ)
    (hb : 0 < b) (hG : Integrable (gaussian b) (μp + μm)) (z : ℂ) :
    AnalyticAt ℂ (momentTransform μp μm) z
```

## `SignedJensenEntirePrep.differentiable_signedPair_nativeKernel`

[JensenMomentEntire.lean,line 311](JensenMomentEntire.lean#L311)

```lean
theorem differentiable_signedPair_nativeKernel (μp μm : Measure U) (b : ℝ)
    (hb : 0 < b) (hG : Integrable (gaussian b) (μp + μm)) :
    Differentiable ℂ (fun z : ℂ => signedPair μp μm (nativeKernel z))
```

## `SignedJensenEntirePrep.analyticAt_signedPair_nativeKernel`

[JensenMomentEntire.lean,line 323](JensenMomentEntire.lean#L323)

```lean
theorem analyticAt_signedPair_nativeKernel (μp μm : Measure U) (b : ℝ)
    (hb : 0 < b) (hG : Integrable (gaussian b) (μp + μm)) (z : ℂ) :
    AnalyticAt ℂ (fun z : ℂ => signedPair μp μm (nativeKernel z)) z
```

## `SignedJensenKernelPrep.factorial_four_real`

[JensenPointwise.lean,line 34](JensenPointwise.lean#L34)

```lean
theorem factorial_four_real (n : ℕ) :
    ((n + 4).factorial : ℝ) =
      ((n : ℝ) + 4) * ((n : ℝ) + 3) * ((n : ℝ) + 2) *
        ((n : ℝ) + 1) * (n.factorial : ℝ)
```

## `SignedJensenKernelPrep.fourth_factor_lower`

[JensenPointwise.lean,line 45](JensenPointwise.lean#L45)

```lean
theorem fourth_factor_lower (k : ℕ) :
    12 * ((k : ℝ) + 2) * ((k : ℝ) + 1) ≤
      (2 * (k : ℝ) + 4) * (2 * (k : ℝ) + 3) *
        (2 * (k : ℝ) + 2) * (2 * (k : ℝ) + 1)
```

## `SignedJensenKernelPrep.factorial_coefficient_shifted`

[JensenPointwise.lean,line 65](JensenPointwise.lean#L65)

```lean
theorem factorial_coefficient_shifted (k : ℕ) :
    (((k : ℝ) + 2) * ((k : ℝ) + 1)) /
        (2 * ((2 * (k + 2)).factorial : ℝ)) ≤
      1 / (24 * ((2 * k).factorial : ℝ))
```

## `SignedJensenKernelPrep.factorial_coefficient_scaled`

[JensenPointwise.lean,line 98](JensenPointwise.lean#L98)

```lean
theorem factorial_coefficient_scaled (k : ℕ) (d : ℝ) (hd : 0 < d) :
    (((k : ℝ) + 2) * ((k : ℝ) + 1)) /
        (2 * d * ((2 * (k + 2)).factorial : ℝ)) ≤
      1 / (24 * d * ((2 * k).factorial : ℝ))
```

## `SignedJensenKernelPrep.factorial_coefficient_at_zero`

[JensenPointwise.lean,line 116](JensenPointwise.lean#L116)

```lean
theorem factorial_coefficient_at_zero :
    ((2 : ℝ) * 1) / (2 * ((4 : ℕ).factorial : ℝ)) = 1 / 24
```

## `SignedJensenKernelPrep.kernelTerm`

[JensenPointwise.lean,line 130](JensenPointwise.lean#L130)

```lean
def kernelTerm (a : ℂ) (j : ℕ) : ℂ
```

## `SignedJensenKernelPrep.completeKernel`

[JensenPointwise.lean,line 133](JensenPointwise.lean#L133)

```lean
def completeKernel (a : ℂ) : ℂ
```

## `SignedJensenKernelPrep.finiteKernel`

[JensenPointwise.lean,line 135](JensenPointwise.lean#L135)

```lean
def finiteKernel (d : ℕ) (a : ℂ) : ℂ
```

## `SignedJensenKernelPrep.errorTerm`

[JensenPointwise.lean,line 138](JensenPointwise.lean#L138)

```lean
def errorTerm (d : ℕ) (a : ℂ) (j : ℕ) : ℂ
```

## `SignedJensenKernelPrep.kernelTerm_norm`

[JensenPointwise.lean,line 141](JensenPointwise.lean#L141)

```lean
theorem kernelTerm_norm (a : ℂ) (j : ℕ) :
    ‖kernelTerm a j‖ = ‖a‖ ^ j / ((2 * j).factorial : ℝ)
```

## `SignedJensenKernelPrep.kernelTerm_norm_le`

[JensenPointwise.lean,line 145](JensenPointwise.lean#L145)

```lean
theorem kernelTerm_norm_le (a : ℂ) (x : ℝ) (ha : ‖a‖ ≤ x ^ 2) (j : ℕ) :
    ‖kernelTerm a j‖ ≤ x ^ (2 * j) / ((2 * j).factorial : ℝ)
```

## `SignedJensenKernelPrep.kernel_summable`

[JensenPointwise.lean,line 155](JensenPointwise.lean#L155)

```lean
theorem kernel_summable (a : ℂ) (x : ℝ) (ha : ‖a‖ ≤ x ^ 2) :
    Summable (kernelTerm a)
```

## `SignedJensenKernelPrep.finiteKernel_hasSum`

[JensenPointwise.lean,line 159](JensenPointwise.lean#L159)

```lean
theorem finiteKernel_hasSum (d : ℕ) (a : ℂ) :
    HasSum (fun j : ℕ => (SignedJensenPrep.weight d j : ℂ) * kernelTerm a j)
      (finiteKernel d a)
```

## `SignedJensenKernelPrep.errorTerm_norm`

[JensenPointwise.lean,line 171](JensenPointwise.lean#L171)

```lean
theorem errorTerm_norm (d j : ℕ) (a : ℂ) (hd : 1 ≤ d) :
    ‖errorTerm d a j‖ = (1 - SignedJensenPrep.weight d j) * ‖kernelTerm a j‖
```

## `SignedJensenKernelPrep.error_coefficient`

[JensenPointwise.lean,line 181](JensenPointwise.lean#L181)

```lean
theorem error_coefficient (d k : ℕ) (hd : 1 ≤ d) :
    (1 - SignedJensenPrep.weight d (k + 2)) /
        ((2 * (k + 2)).factorial : ℝ) ≤
      1 / (24 * (d : ℝ) * ((2 * k).factorial : ℝ))
```

## `SignedJensenKernelPrep.shifted_error_bound`

[JensenPointwise.lean,line 201](JensenPointwise.lean#L201)

```lean
theorem shifted_error_bound (d k : ℕ) (hd : 1 ≤ d)
    (a : ℂ) (x : ℝ) (hx : 0 ≤ x) (ha : ‖a‖ ≤ x ^ 2) :
    ‖errorTerm d a (k + 2)‖ ≤
      x ^ 4 / (24 * (d : ℝ)) * (x ^ (2 * k) / ((2 * k).factorial : ℝ))
```

## `SignedJensenKernelPrep.finite_prefix_bound`

[JensenPointwise.lean,line 223](JensenPointwise.lean#L223)

```lean
theorem finite_prefix_bound (d n : ℕ) (hd : 1 ≤ d)
    (a : ℂ) (x : ℝ) (hx : 0 ≤ x) (ha : ‖a‖ ≤ x ^ 2) :
    ‖∑ k ∈ Finset.range n, errorTerm d a (k + 2)‖ ≤
      x ^ 4 / (24 * (d : ℝ)) *
        ∑ k ∈ Finset.range n, x ^ (2 * k) / ((2 * k).factorial : ℝ)
```

## `SignedJensenKernelPrep.kernel_error_hasSum`

[JensenPointwise.lean,line 235](JensenPointwise.lean#L235)

```lean
theorem kernel_error_hasSum (d : ℕ) (hd : 1 ≤ d)
    (a : ℂ) (x : ℝ) (ha : ‖a‖ ≤ x ^ 2) :
    HasSum (fun k : ℕ => errorTerm d a (k + 2))
      (finiteKernel d a - completeKernel a)
```

## `SignedJensenKernelPrep.pointwise_kernel_aux`

[JensenPointwise.lean,line 255](JensenPointwise.lean#L255)

```lean
theorem pointwise_kernel_aux (d : ℕ) (hd : 1 ≤ d)
    (a : ℂ) (x : ℝ) (hx : 0 ≤ x) (ha : ‖a‖ ≤ x ^ 2) :
    ‖finiteKernel d a - completeKernel a‖ ≤
      x ^ 4 / (24 * (d : ℝ)) * Real.cosh x
```

## `SignedJensenKernelPrep.kernelTerm_native`

[JensenPointwise.lean,line 263](JensenPointwise.lean#L263)

```lean
theorem kernelTerm_native (z : ℂ) (u : ℝ) (j : ℕ) :
    kernelTerm (z * (u : ℂ) ^ 2) j =
      (-1 : ℂ) ^ j * z ^ j * (u : ℂ) ^ (2 * j) /
        ((2 * j).factorial : ℂ)
```

## `SignedJensenKernelPrep.pointwise_kernel_disk`

[JensenPointwise.lean,line 271](JensenPointwise.lean#L271)

```lean
theorem pointwise_kernel_disk (d : ℕ) (hd : 1 ≤ d)
    (z : ℂ) (u r : ℝ) (hu : 0 ≤ u) (hr : 0 ≤ r) (hz : ‖z‖ ≤ r) :
    ‖finiteKernel d (z * (u : ℂ) ^ 2) - completeKernel (z * (u : ℂ) ^ 2)‖ ≤
      (r ^ 2 * u ^ 4) / (24 * (d : ℝ)) * Real.cosh (Real.sqrt r * u)
```

## `SignedJensenPrep.rawWeight`

[JensenWeights.lean,line 25](JensenWeights.lean#L25)

```lean
def rawWeight (d j : ℕ) : ℝ
```

## `SignedJensenPrep.weight`

[JensenWeights.lean,line 29](JensenWeights.lean#L29)

```lean
def weight (d j : ℕ) : ℝ
```

## `SignedJensenPrep.rawWeight_zero`

[JensenWeights.lean,line 32](JensenWeights.lean#L32)

```lean
theorem rawWeight_zero (d : ℕ) : rawWeight d 0 = 1
```

## `SignedJensenPrep.rawWeight_succ`

[JensenWeights.lean,line 35](JensenWeights.lean#L35)

```lean
theorem rawWeight_succ (d j : ℕ) :
    rawWeight d (j + 1) = rawWeight d j * (1 - (j : ℝ) / (d : ℝ))
```

## `SignedJensenPrep.rawWeight_bounds`

[JensenWeights.lean,line 40](JensenWeights.lean#L40)

```lean
theorem rawWeight_bounds (d : ℕ) (hd : 1 ≤ d) :
    ∀ j : ℕ, j ≤ d →
      0 ≤ rawWeight d j ∧ rawWeight d j ≤ 1 ∧
        1 - rawWeight d j ≤ (j : ℝ) * ((j : ℝ) - 1) / (2 * (d : ℝ))
```

## `SignedJensenPrep.weight_zero`

[JensenWeights.lean,line 90](JensenWeights.lean#L90)

```lean
theorem weight_zero (d : ℕ) : weight d 0 = 1
```

## `SignedJensenPrep.weight_one`

[JensenWeights.lean,line 93](JensenWeights.lean#L93)

```lean
theorem weight_one (d : ℕ) (hd : 1 ≤ d) : weight d 1 = 1
```

## `SignedJensenPrep.weight_eq_zero_of_lt`

[JensenWeights.lean,line 96](JensenWeights.lean#L96)

```lean
theorem weight_eq_zero_of_lt {d j : ℕ} (h : d < j) : weight d j = 0
```

## `SignedJensenPrep.weight_bounds`

[JensenWeights.lean,line 100](JensenWeights.lean#L100)

```lean
theorem weight_bounds (d j : ℕ) (hd : 1 ≤ d) :
    0 ≤ weight d j ∧ weight d j ≤ 1 ∧
      1 - weight d j ≤ (j : ℝ) * ((j : ℝ) - 1) / (2 * (d : ℝ))
```

## `SignedJensenPrep.weight_two`

[JensenWeights.lean,line 125](JensenWeights.lean#L125)

```lean
theorem weight_two (d : ℕ) (hd : 1 ≤ d) :
    weight d 2 = 1 - 1 / (d : ℝ)
```
