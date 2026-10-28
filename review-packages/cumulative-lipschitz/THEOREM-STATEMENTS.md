# Exact four-contract API

These are the public types in [Cumulative.lean](Cumulative.lean), in namespace `MeasureTheory`. The cumulative uses `Iic`; its outer cost is integrated against Lebesgue measure. No finite or `SFinite` premise is imposed on the original measure.

## Weighted test integrability

```lean
theorem integrable_lipschitz_mul {μ : Measure ℝ} {d w : ℝ → ℝ}
    (hd : Integrable d μ) (hm : Integrable (fun x => x * d x) μ)
    (hw : LipschitzWith 1 w) :
    Integrable (fun x => w x * d x) μ
```

## Cumulative measurability and integrability

```lean
theorem measurable_integrable_setIntegral_Iic {μ : Measure ℝ} {d : ℝ → ℝ}
    (hd : Integrable d μ) (hm : Integrable (fun x => x * d x) μ)
    (hz : (∫ x, d x ∂μ) = 0) :
    Measurable (fun t : ℝ => ∫ x in Iic t, d x ∂μ) ∧
      Integrable (fun t : ℝ => ∫ x in Iic t, d x ∂μ) volume
```

## Attaining Lipschitz test

```lean
theorem exists_lipschitz_cumulative_attainer {μ : Measure ℝ} {d : ℝ → ℝ}
    (hd : Integrable d μ) (hm : Integrable (fun x => x * d x) μ)
    (hz : (∫ x, d x ∂μ) = 0) :
    ∃ w : ℝ → ℝ, LipschitzWith 1 w ∧ Integrable (fun x => w x * d x) μ ∧
      (∫ x, w x * d x ∂μ) = ∫ t : ℝ, |∫ x in Iic t, d x ∂μ|
```

## Sharp budget equivalence

```lean
theorem forall_lipschitz_abs_integral_mul_le_iff {μ : Measure ℝ} {d : ℝ → ℝ}
    (hd : Integrable d μ) (hm : Integrable (fun x => x * d x) μ)
    (hz : (∫ x, d x ∂μ) = 0) (B : ℝ) :
    (∀ w : ℝ → ℝ, LipschitzWith 1 w → |∫ x, w x * d x ∂μ| ≤ B) ↔
      (∫ t : ℝ, |∫ x in Iic t, d x ∂μ|) ≤ B
```

The first theorem does not require zero total mass. The other three do. The attainer theorem includes actual weighted integrability. The final theorem quantifies over every real B and every real 1-Lipschitz test; it adds neither B ≥ 0 nor test-integrability as a hypothesis. These contracts do not assert that a particular application satisfies their assumptions.
