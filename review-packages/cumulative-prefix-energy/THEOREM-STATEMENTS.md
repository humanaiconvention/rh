# Exact package-owned statements and hypotheses

These are the unchanged public source headers, with proof introductions or definition bodies omitted. Shared context is `variable {ι : Type*}`, real-valued functions and Lebesgue interval integration. `CumulativeSquareEnergy` uses `open Set Filter MeasureTheory` and `open scoped BigOperators Topology`; `CumulativePrefixBilinear` opens `CumulativeSquareEnergy`, `Set`, `MeasureTheory` and `BigOperators`.

The main finite-prefix theorems use one common `s : Finset ι`, `p c e : ι → ℝ`, `∀ i ∈ s, 0 < p i`, and `0 < a ≤ b`. No injectivity, sign, balance, nonemptiness, support-inside-window or endpoint-avoidance assumption is imposed. Coincident sites, signed coefficients, the empty family and `a=b` are allowed. No complex or infinite-prefix theorem, or independent-list reindexing theorem, is exported here.

The inclusive prefix is `M_c(t) = ∑ i ∈ s, if p i ≤ t then c i else 0`; `g_c(t)` replaces each coefficient by `c i / p i`; and `γ_c(t) = g_c(t) - M_c(t)/t`. The atom is zero before its site and `c/p - c/t` at and after it. Terminal energy statements require positive sites and `a>0`; the totalized division definitions do not assert an analytic result at zero.

The compensated function is continuous on positive arguments and has a **right derivative**, `HasDerivWithinAt ... (Ioi t) t`, at positive sites as well as elsewhere. It need not have an ordinary two-sided derivative at a site. The generic `square_energy_of_right_derivative` assumes its displayed continuity, right-derivative and integrability premises. The actual finite-prefix terminal theorems prove the required integrability internally.

There are eighteen public theorems and four definitions below. Two private polarization helpers are not public API. Ten declarations have saved terminal axiom reports; the remaining eight compiled public theorems are listed explicitly in the [roster](evidence/public-declarations.json), without implying a separate historical report for each.

## `CumulativeSquareEnergy.prefixMass`

[CumulativeSquareEnergy.lean, line 26](CumulativeSquareEnergy.lean#L26)

```lean
def prefixMass (s : Finset ι) (p c : ι → ℝ) (t : ℝ) : ℝ
```

## `CumulativeSquareEnergy.weightedPrefix`

[CumulativeSquareEnergy.lean, line 29](CumulativeSquareEnergy.lean#L29)

```lean
def weightedPrefix (s : Finset ι) (p c : ι → ℝ) (t : ℝ) : ℝ
```

## `CumulativeSquareEnergy.compensated`

[CumulativeSquareEnergy.lean, line 32](CumulativeSquareEnergy.lean#L32)

```lean
def compensated (s : Finset ι) (p c : ι → ℝ) (t : ℝ) : ℝ
```

## `CumulativeSquareEnergy.atomCompensated`

[CumulativeSquareEnergy.lean, line 35](CumulativeSquareEnergy.lean#L35)

```lean
def atomCompensated (p c t : ℝ) : ℝ
```

## `CumulativeSquareEnergy.compensated_eq_sum`

[CumulativeSquareEnergy.lean, line 38](CumulativeSquareEnergy.lean#L38)

```lean
theorem compensated_eq_sum (s : Finset ι) (p c : ι → ℝ) (t : ℝ) :
    compensated s p c t = ∑ i ∈ s, atomCompensated (p i) (c i) t
```

## `CumulativeSquareEnergy.atomCompensated_eq_max`

[CumulativeSquareEnergy.lean, line 46](CumulativeSquareEnergy.lean#L46)

```lean
theorem atomCompensated_eq_max {p c t : ℝ} (hp : 0 < p) (ht : 0 < t) :
    atomCompensated p c t = c * max (t - p) 0 / (p * t)
```

## `CumulativeSquareEnergy.atomCompensated_continuousOn`

[CumulativeSquareEnergy.lean, line 54](CumulativeSquareEnergy.lean#L54)

```lean
theorem atomCompensated_continuousOn {p c : ℝ} (hp : 0 < p) :
    ContinuousOn (atomCompensated p c) (Ioi 0)
```

## `CumulativeSquareEnergy.atomCompensated_hasDeriv_right`

[CumulativeSquareEnergy.lean, line 65](CumulativeSquareEnergy.lean#L65)

```lean
theorem atomCompensated_hasDeriv_right {p c t : ℝ} (ht : 0 < t) :
    HasDerivWithinAt (atomCompensated p c)
      (if p ≤ t then c / t ^ 2 else 0) (Ioi t) t
```

## `CumulativeSquareEnergy.compensated_continuousOn`

[CumulativeSquareEnergy.lean, line 86](CumulativeSquareEnergy.lean#L86)

```lean
theorem compensated_continuousOn (s : Finset ι) (p c : ι → ℝ)
    (hp : ∀ i ∈ s, 0 < p i) : ContinuousOn (compensated s p c) (Ioi 0)
```

## `CumulativeSquareEnergy.compensated_hasDeriv_right`

[CumulativeSquareEnergy.lean, line 92](CumulativeSquareEnergy.lean#L92)

```lean
theorem compensated_hasDeriv_right (s : Finset ι) (p c : ι → ℝ) {t : ℝ}
    (ht : 0 < t) : HasDerivWithinAt (compensated s p c)
      (prefixMass s p c t / t ^ 2) (Ioi t) t
```

## `CumulativeSquareEnergy.prefixMass_measurable`

[CumulativeSquareEnergy.lean, line 107](CumulativeSquareEnergy.lean#L107)

```lean
theorem prefixMass_measurable (s : Finset ι) (p c : ι → ℝ) :
    Measurable (prefixMass s p c)
```

## `CumulativeSquareEnergy.prefixMass_norm_le`

[CumulativeSquareEnergy.lean, line 115](CumulativeSquareEnergy.lean#L115)

```lean
theorem prefixMass_norm_le (s : Finset ι) (p c : ι → ℝ) (t : ℝ) :
    ‖prefixMass s p c t‖ ≤ ∑ i ∈ s, ‖c i‖
```

## `CumulativeSquareEnergy.prefixMass_sq_intervalIntegrable`

[CumulativeSquareEnergy.lean, line 125](CumulativeSquareEnergy.lean#L125)

```lean
theorem prefixMass_sq_intervalIntegrable (s : Finset ι) (p c : ι → ℝ)
    {a b : ℝ} (hab : a ≤ b) :
    IntervalIntegrable (fun t => prefixMass s p c t ^ 2) volume a b
```

## `CumulativeSquareEnergy.square_energy_of_right_derivative`

[CumulativeSquareEnergy.lean, line 137](CumulativeSquareEnergy.lean#L137)

```lean
theorem square_energy_of_right_derivative {g M γ : ℝ → ℝ} {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hc : ContinuousOn γ (Icc a b))
    (hd : ∀ t ∈ Ioo a b, HasDerivWithinAt γ (M t / t ^ 2) (Ioi t) t)
    (hg : ∀ t ∈ Icc a b, g t = γ t + M t / t)
    (hgi : IntervalIntegrable (fun t => g t ^ 2) volume a b)
    (hMi : IntervalIntegrable (fun t => M t ^ 2 / t ^ 2) volume a b) :
    (∫ t in a..b, g t ^ 2) = b * γ b ^ 2 - a * γ a ^ 2 +
      ∫ t in a..b, M t ^ 2 / t ^ 2
```

## `CumulativeSquareEnergy.finite_prefix_square_energy`

[CumulativeSquareEnergy.lean, line 167](CumulativeSquareEnergy.lean#L167)

```lean
theorem finite_prefix_square_energy (s : Finset ι) (p c : ι → ℝ)
    (hp : ∀ i ∈ s, 0 < p i) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ t in a..b, weightedPrefix s p c t ^ 2) =
      b * compensated s p c b ^ 2 - a * compensated s p c a ^ 2 +
        ∫ t in a..b, prefixMass s p c t ^ 2 / t ^ 2
```

## `CumulativeSquareEnergy.nat_prefix_square_energy`

[CumulativeSquareEnergy.lean, line 190](CumulativeSquareEnergy.lean#L190)

```lean
theorem nat_prefix_square_energy (N : ℕ) (c : ℕ → ℝ) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) :
    (∫ t in a..b, weightedPrefix (Finset.Icc 1 N) (fun n => (n : ℝ)) c t ^ 2) =
      b * compensated (Finset.Icc 1 N) (fun n => (n : ℝ)) c b ^ 2 -
      a * compensated (Finset.Icc 1 N) (fun n => (n : ℝ)) c a ^ 2 +
        ∫ t in a..b, prefixMass (Finset.Icc 1 N) (fun n => (n : ℝ)) c t ^ 2 / t ^ 2
```

## `CumulativeSquareEnergy.single_atom_left_endpoint`

[CumulativeSquareEnergy.lean, line 202](CumulativeSquareEnergy.lean#L202)

```lean
theorem single_atom_left_endpoint {q c b : ℝ} (hq : 0 < q) (hqb : q ≤ b) :
    (∫ t in q..b, weightedPrefix ({0} : Finset ℕ) (fun _ => q) (fun _ => c) t ^ 2) =
      b * (c / q - c / b) ^ 2 +
        ∫ t in q..b, prefixMass ({0} : Finset ℕ) (fun _ => q) (fun _ => c) t ^ 2 / t ^ 2
```

## `CumulativePrefixBilinear.prefixMass_add`

[FinitePrefixBilinear.lean, line 20](FinitePrefixBilinear.lean#L20)

```lean
theorem prefixMass_add (s : Finset ι) (p c e : ι → ℝ) (t : ℝ) :
    prefixMass s p (fun i => c i + e i) t =
      prefixMass s p c t + prefixMass s p e t
```

## `CumulativePrefixBilinear.weightedPrefix_add`

[FinitePrefixBilinear.lean, line 29](FinitePrefixBilinear.lean#L29)

```lean
theorem weightedPrefix_add (s : Finset ι) (p c e : ι → ℝ) (t : ℝ) :
    weightedPrefix s p (fun i => c i + e i) t =
      weightedPrefix s p c t + weightedPrefix s p e t
```

## `CumulativePrefixBilinear.compensated_add`

[FinitePrefixBilinear.lean, line 36](FinitePrefixBilinear.lean#L36)

```lean
theorem compensated_add (s : Finset ι) (p c e : ι → ℝ) (t : ℝ) :
    compensated s p (fun i => c i + e i) t =
      compensated s p c t + compensated s p e t
```

## `CumulativePrefixBilinear.prefixMass_mul_intervalIntegrable`

[FinitePrefixBilinear.lean, line 45](FinitePrefixBilinear.lean#L45)

```lean
theorem prefixMass_mul_intervalIntegrable (s : Finset ι) (p c e : ι → ℝ)
    {a b : ℝ} (hab : a ≤ b) :
    IntervalIntegrable
      (fun t => prefixMass s p c t * prefixMass s p e t) volume a b
```

## `CumulativePrefixBilinear.finite_prefix_bilinear_energy`

[FinitePrefixBilinear.lean, line 97](FinitePrefixBilinear.lean#L97)

```lean
theorem finite_prefix_bilinear_energy (s : Finset ι) (p c e : ι → ℝ)
    (hp : ∀ i ∈ s, 0 < p i) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ t in a..b, weightedPrefix s p c t * weightedPrefix s p e t) =
      b * compensated s p c b * compensated s p e b -
      a * compensated s p c a * compensated s p e a +
        ∫ t in a..b, prefixMass s p c t * prefixMass s p e t / t ^ 2
```
