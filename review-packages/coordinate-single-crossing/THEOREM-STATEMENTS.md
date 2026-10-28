# Exact five-contract API

The following are the unchanged public types in [CoordinateSingleCrossing.lean](CoordinateSingleCrossing.lean). The shared ambient variables are shown explicitly. Integrals are against μ unless another measure is written.

```lean
open MeasureTheory Filter
open scoped NNReal

namespace CoordinateSingleCrossing

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
  {d ψ : α → ℝ} {φ : ℝ → ℝ} {a : ℝ} {K : ℝ≥0}

theorem lipschitz_comp_mul_integrable
    (hψ : AEMeasurable ψ μ) (hd : Integrable d μ)
    (hm : Integrable (fun x => ψ x * d x) μ) (hφ : LipschitzWith K φ) :
    Integrable (fun x => φ (ψ x) * d x) μ

theorem centered_coordinate_moment_eq
    (hd : Integrable d μ) (hm : Integrable (fun x => ψ x * d x) μ)
    (hzero : (∫ x, d x ∂μ) = 0) :
    (∫ x, (ψ x - a) * d x ∂μ) = ∫ x, ψ x * d x ∂μ

theorem coordinate_moment_nonneg
    (hd : Integrable d μ) (hm : Integrable (fun x => ψ x * d x) μ)
    (hzero : (∫ x, d x ∂μ) = 0)
    (hsign : ∀ᵐ x ∂μ, 0 ≤ (ψ x - a) * d x) :
    0 ≤ ∫ x, ψ x * d x ∂μ

theorem abs_integral_comp_le_coordinate_moment
    (hψ : AEMeasurable ψ μ) (hd : Integrable d μ)
    (hm : Integrable (fun x => ψ x * d x) μ)
    (hzero : (∫ x, d x ∂μ) = 0)
    (hsign : ∀ᵐ x ∂μ, 0 ≤ (ψ x - a) * d x)
    (hφ : LipschitzWith K φ) :
    |∫ x, φ (ψ x) * d x ∂μ| ≤ (K : ℝ) * ∫ x, ψ x * d x ∂μ

theorem universal_coordinate_budget_iff
    (hψ : AEMeasurable ψ μ) (hd : Integrable d μ)
    (hm : Integrable (fun x => ψ x * d x) μ)
    (hzero : (∫ x, d x ∂μ) = 0)
    (hsign : ∀ᵐ x ∂μ, 0 ≤ (ψ x - a) * d x) {B : ℝ} :
    (∀ φ : ℝ → ℝ, LipschitzWith 1 φ → |∫ x, φ (ψ x) * d x ∂μ| ≤ B) ↔
      (∫ x, ψ x * d x ∂μ) ≤ B

end CoordinateSingleCrossing
```

The centered identity and moment nonnegativity theorem require no separate `hψ` hypothesis. The composition-integrability and Lipschitz-comparison theorems do require it. Integrability of ψd alone is not used as a substitute for AE measurability of ψ.

The first result needs neither zero mass nor a sign condition. The comparison allows every `K : ℝ≥0`, including zero. The final equivalence concerns unit Lipschitz tests and every real B, without a B ≥ 0 premise or a separately assumed integrability condition on those tests. No theorem asserts strictness or constructs a crossing for a particular application.
