# Exact definition and seven-contract API

The following are the unchanged public definition and theorem types in [ThetaPowerCoordinate.lean](ThetaPowerCoordinate.lean). The actual density definitions are given in [SOURCE-DEFINITIONS.md](SOURCE-DEFINITIONS.md). Every displayed set integral is a Lebesgue integral on the positive half-line.

```lean
open Set MeasureTheory Filter
open scoped NNReal

namespace ThetaMacdonald.PowerCoordinate
open Density Mass Cumulative Moment

def powerMomentGap (k : ℕ) : ℝ :=
  (∫ u in Ioi (0 : ℝ), u^k * thetaDensity u) -
    ∫ u in Ioi (0 : ℝ), u^k * macdonaldDensity u

theorem powerMomentGap_pos (k : ℕ) (hk : 0 < k) : 0 < powerMomentGap k

theorem powerMomentGap_eq_signed (k : ℕ) :
    powerMomentGap k = ∫ u in Ioi (0 : ℝ), u^k * densityDifference u

theorem actual_power_coordinate_measurable (k : ℕ) :
    AEMeasurable (fun u : ℝ => u^k) (volume.restrict (Ioi (0 : ℝ)))

theorem actual_power_crossing_ae (k : ℕ) :
    ∃ a : ℝ, ∀ᵐ u ∂(volume.restrict (Ioi (0 : ℝ))),
      0 ≤ (u^k - a) * densityDifference u

theorem actual_power_weighted_integrable (k : ℕ) {φ : ℝ → ℝ} {K : ℝ≥0}
    (hφ : LipschitzWith K φ) :
    IntegrableOn (fun u => φ (u^k) * thetaDensity u) (Ioi (0 : ℝ)) ∧
      IntegrableOn (fun u => φ (u^k) * macdonaldDensity u) (Ioi (0 : ℝ))

theorem actual_power_lipschitz_gap_le (k : ℕ) {φ : ℝ → ℝ} {K : ℝ≥0}
    (hφ : LipschitzWith K φ) :
    |(∫ u in Ioi (0 : ℝ), φ (u^k) * thetaDensity u) -
      ∫ u in Ioi (0 : ℝ), φ (u^k) * macdonaldDensity u| ≤
        (K : ℝ) * powerMomentGap k

theorem actual_positive_power_budget_iff (k : ℕ) (hk : 0 < k) {B : ℝ} :
    (∀ φ : ℝ → ℝ, LipschitzWith 1 φ →
      |(∫ u in Ioi (0 : ℝ), φ (u^k) * thetaDensity u) -
        ∫ u in Ioi (0 : ℝ), φ (u^k) * macdonaldDensity u| ≤ B) ↔
      powerMomentGap k ≤ B

end ThetaMacdonald.PowerCoordinate
```

Only strict positivity and the exported sharp-budget equivalence require `0 < k`. The equality, AE measurability, AE sign condition, weighted integrability and gap bound hold for every natural k. `K : ℝ≥0` includes zero. The final equivalence uses unit Lipschitz tests and every real B, with no B ≥ 0 premise or extra test-integrability assumption.

There are no additional user-level normalization, crossing, moment-integrability or source-positivity premises in these declarations. Their proofs use the actual bundled providers, listed in [DEPS.json](DEPS.json). The theorem family does not replace k by a real exponent, claim a uniform numerical bound in k, or assume that φ(u^k) is Lipschitz in physical u.
