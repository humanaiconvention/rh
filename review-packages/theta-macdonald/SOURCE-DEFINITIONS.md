# Actual complete sources and exact normalizers

The reader notation is `z_k(u)=πk²exp(2u)` and `Phi(u)=∑_{k≥0}(8z_k(u)²−12z_k(u))exp(u/2−z_k(u))`. The zero shell vanishes. This is the complete infinite source,not a finite shell prefix. The selected definitions below are copied once each from the accepted sources. The older frozen editorial note repeated some definition blocks;this new portable note removes only those repetitions,without changing a Lean byte or mathematical definition.

The actual normalized densities are `thetaDensity=thetaProfile/gamma0` and `macdonaldDensity(u)=2*exp(-2π*cosh(2u))/macdonaldK0(2π)`. The K0 definition is its positive-half-line integral;integrability and positivity are proved for x>0. Its source's DLMF10.32.9 attribution and pinned-library commentary remain historical,not a fresh global API-absence claim.

## `ThetaMacdonald.zArg`

[ThetaShellDerivative.lean,line 13](ThetaShellDerivative.lean#L13)

```lean
def zArg (k : ℕ) (u : ℝ) : ℝ := Real.pi * (k : ℝ)^2 * Real.exp (2*u)
```

## `ThetaMacdonald.rawShell`

[ThetaShellDerivative.lean,line 15](ThetaShellDerivative.lean#L15)

```lean
def rawShell (k : ℕ) (u : ℝ) : ℝ :=
  (8 * zArg k u ^ 2 - 12 * zArg k u) * Real.exp (u/2 - zArg k u)
```

## `ThetaMacdonald.Density.thetaProfile`

[ThetaMassBounds.lean,line 13](ThetaMassBounds.lean#L13)

```lean
def thetaProfile (u : ℝ) : ℝ := ∑' k : ℕ, rawShell k u
```

## `ThetaMacdonald.Density.thetaMass`

[ThetaMassBounds.lean,line 14](ThetaMassBounds.lean#L14)

```lean
def thetaMass : ℝ := ∫ u in Ioi (0 : ℝ), thetaProfile u
```

## `ThetaMacdonald.Mass.gamma0`

[ThetaMellinMass.lean,line 140](ThetaMellinMass.lean#L140)

```lean
def gamma0 : ℝ :=
  (1+(1/2 : ℂ)*((1/2 : ℂ)-1)*completedRiemannZeta₀ (1/2 : ℂ)).re/2
```

## `ThetaMacdonald.Mass.xiHalf`

[ThetaProbabilityMass.lean,line 13](ThetaProbabilityMass.lean#L13)

```lean
def xiHalf : ℂ :=
  ((1/2 : ℂ)*((1/2 : ℂ)-1)*Complex.Gammaℝ (1/2 : ℂ)*
    riemannZeta (1/2 : ℂ))/2
```

## `ThetaMacdonald.Mass.thetaDensity`

[ThetaProbabilityMass.lean,line 58](ThetaProbabilityMass.lean#L58)

```lean
def thetaDensity (u : ℝ) : ℝ := thetaProfile u/gamma0
```

## `ThetaMacdonald.Density.macdonaldKernel`

[MacdonaldMass.lean,line 14](MacdonaldMass.lean#L14)

```lean
def macdonaldKernel (x t : ℝ) : ℝ := Real.exp (-x * Real.cosh t)
```

## `ThetaMacdonald.Density.macdonaldK0`

[MacdonaldMass.lean,line 15](MacdonaldMass.lean#L15)

```lean
def macdonaldK0 (x : ℝ) : ℝ := ∫ t in Ioi (0 : ℝ), macdonaldKernel x t
```

## `ThetaMacdonald.Density.macdonaldDensity`

[MacdonaldMass.lean,line 16](MacdonaldMass.lean#L16)

```lean
def macdonaldDensity (u : ℝ) : ℝ :=
  2 * macdonaldKernel (2 * Real.pi) (2*u) / macdonaldK0 (2 * Real.pi)
```

## Proved normalization dictionary

`ThetaMacdonald.Mass.thetaMass_eq_gamma0` and `gamma0_pos` identify the actual positive half-line mass and its positive arithmetic normalizer. `xiHalf_eq_gamma0` states `xiHalf=(gamma0:ℂ)`. Here `xiHalf` is the standard expression `s*(s-1)*Complex.Gammaℝ(s)*riemannZeta(s)/2` at s=1/2;the real/complex embedding is explicit. It is not a renamed totalized density integral.

`ThetaMacdonald.Mass.thetaDensity_mass`, `ThetaMacdonald.Density.macdonaldDensity_mass` and `actual_equal_probability_masses` give actual unit masses on `Ioi 0`,with positivity and integrability separately proved. The Mellin/standard-zeta providers are included in the complete local closure. Their RhWeil filenames do not import an explicit-formula or RH assumption.

[Exact statements](THEOREM-STATEMENTS.md), [source/evidence map](DEPENDENCY-HANDOFF.md).
