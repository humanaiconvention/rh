# Complete source definitions and normalization

The complete theta profile uses z_n(u)=πn²exp(2u) and every natural shell. The zero shell vanishes. No finite shell prefix replaces the sum below. The selected blocks are the actual definitions in the package-local Lean providers; [DEPS.json](DEPS.json) records their identities and dependency relationships.

## Theta shells and profile

From [ThetaShellDerivative.lean](ThetaShellDerivative.lean), in namespace `ThetaMacdonald`:

```lean
def zArg (k : ℕ) (u : ℝ) : ℝ := Real.pi * (k : ℝ)^2 * Real.exp (2*u)

def rawShell (k : ℕ) (u : ℝ) : ℝ :=
  (8 * zArg k u ^ 2 - 12 * zArg k u) * Real.exp (u/2 - zArg k u)
```

From [ThetaMassBounds.lean](ThetaMassBounds.lean), in namespace `ThetaMacdonald.Density`:

```lean
def thetaProfile (u : ℝ) : ℝ := ∑' k : ℕ, rawShell k u
def thetaMass : ℝ := ∫ u in Ioi (0 : ℝ), thetaProfile u
```

Convergence, derivative control, positive half-line mass and the tail bounds used for moment integrability are provider theorems, not assumptions added to the power-coordinate API.

## Arithmetic normalizer and normalized theta density

From [ThetaMellinMass.lean](ThetaMellinMass.lean), in namespace `ThetaMacdonald.Mass`:

```lean
def gamma0 : ℝ :=
  (1+(1/2 : ℂ)*((1/2 : ℂ)-1)*completedRiemannZeta₀ (1/2 : ℂ)).re/2
```

From [ThetaProbabilityMass.lean](ThetaProbabilityMass.lean), in the same namespace:

```lean
def xiHalf : ℂ :=
  ((1/2 : ℂ)*((1/2 : ℂ)-1)*Complex.Gammaℝ (1/2 : ℂ)*
    riemannZeta (1/2 : ℂ))/2

def thetaDensity (u : ℝ) : ℝ := thetaProfile u/gamma0
```

Here `Complex.Gammaℝ(s)=π^(-s/2)Γ(s/2)` follows Mathlib's convention. Thus `xiHalf` is classical ξ(1/2). The proved dictionary is `thetaMass_eq_gamma0`, `gamma0_pos`, `xiHalf_eq_gamma0` with conclusion `xiHalf = (gamma0 : ℂ)`, and `thetaDensity_mass` with unit mass on `Ioi 0`. The normalizer is not introduced by merely renaming the theta integral.

## Macdonald density

From [MacdonaldMass.lean](MacdonaldMass.lean), in namespace `ThetaMacdonald.Density`:

```lean
def macdonaldKernel (x t : ℝ) : ℝ := Real.exp (-x * Real.cosh t)
def macdonaldK0 (x : ℝ) : ℝ := ∫ t in Ioi (0 : ℝ), macdonaldKernel x t
def macdonaldDensity (u : ℝ) : ℝ :=
  2 * macdonaldKernel (2 * Real.pi) (2*u) / macdonaldK0 (2 * Real.pi)
```

This is the classical positive-real integral representation of K₀. Its integrability and positivity for x > 0, and the actual density's integrability and unit mass, are proved in that provider. The historical source attribution to the integral representation is retained; no current-library API-absence claim is made here.

## Difference, moments and actual crossing

From [ThetaCumulativeOrder.lean](ThetaCumulativeOrder.lean), in namespace `ThetaMacdonald.Cumulative`:

```lean
def densityDifference (t : ℝ) : ℝ := thetaDensity t-macdonaldDensity t
```

`integrable_densityDifference` and `integral_densityDifference_zero` give the actual signed mass inputs. [ThetaDensityCrossing.lean](ThetaDensityCrossing.lean) supplies a positive crossing c and the strict density sides on the nonnegative half-line. [ThetaMomentOrder.lean](ThetaMomentOrder.lean) proves integrability of both densities and their difference against every natural power, plus strict power-moment order for positive exponents. The power-coordinate source converts the crossing into the AE inequality with threshold c^k on `(0,∞)`.
