import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Tactic.Ring

/-! Signed single-crossing transport along an explicitly AE-measurable real
coordinate on an arbitrary measurable space. No pushforward/coupling is assumed. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal
namespace CoordinateSingleCrossing

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
  {d ψ : α → ℝ} {φ : ℝ → ℝ} {a : ℝ} {K : ℝ≥0}

theorem lipschitz_comp_mul_integrable
    (hψ : AEMeasurable ψ μ) (hd : Integrable d μ)
    (hm : Integrable (fun x => ψ x * d x) μ) (hφ : LipschitzWith K φ) :
    Integrable (fun x => φ (ψ x) * d x) μ := by
  have hbound (x : α) :
      ‖(φ (ψ x) - φ 0) * d x‖ ≤ (K : ℝ) * ‖ψ x * d x‖ := by
    have hlip : ‖φ (ψ x) - φ 0‖ ≤ (K : ℝ) * ‖ψ x‖ := by
      simpa only [Real.dist_eq, Real.norm_eq_abs, sub_zero] using hφ.dist_le_mul (ψ x) 0
    calc
      _ = ‖φ (ψ x) - φ 0‖ * ‖d x‖ := norm_mul _ _
      _ ≤ ((K : ℝ) * ‖ψ x‖) * ‖d x‖ :=
        mul_le_mul_of_nonneg_right hlip (norm_nonneg _)
      _ = _ := by rw [norm_mul]; ring
  have hcenter : Integrable (fun x => (φ (ψ x) - φ 0) * d x) μ := by
    apply (hm.norm.const_mul (K : ℝ)).mono'
      (((hφ.continuous.sub continuous_const).comp_aestronglyMeasurable
        hψ.aestronglyMeasurable).mul hd.aestronglyMeasurable)
    exact Eventually.of_forall hbound
  apply (hcenter.add (hd.const_mul (φ 0))).congr
  exact Eventually.of_forall (fun x => by dsimp; ring)

theorem centered_coordinate_moment_eq
    (hd : Integrable d μ) (hm : Integrable (fun x => ψ x * d x) μ)
    (hzero : (∫ x, d x ∂μ) = 0) :
    (∫ x, (ψ x - a) * d x ∂μ) = ∫ x, ψ x * d x ∂μ := by
  calc
    _ = ∫ x, ψ x * d x - a * d x ∂μ := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun x => by ring)
    _ = _ := by rw [integral_sub hm (hd.const_mul a), integral_const_mul,
      hzero, mul_zero, sub_zero]

theorem coordinate_moment_nonneg
    (hd : Integrable d μ) (hm : Integrable (fun x => ψ x * d x) μ)
    (hzero : (∫ x, d x ∂μ) = 0)
    (hsign : ∀ᵐ x ∂μ, 0 ≤ (ψ x - a) * d x) :
    0 ≤ ∫ x, ψ x * d x ∂μ := by
  rw [← centered_coordinate_moment_eq (a := a) hd hm hzero]
  exact integral_nonneg_of_ae hsign

theorem abs_integral_comp_le_coordinate_moment
    (hψ : AEMeasurable ψ μ) (hd : Integrable d μ)
    (hm : Integrable (fun x => ψ x * d x) μ)
    (hzero : (∫ x, d x ∂μ) = 0)
    (hsign : ∀ᵐ x ∂μ, 0 ≤ (ψ x - a) * d x)
    (hφ : LipschitzWith K φ) :
    |∫ x, φ (ψ x) * d x ∂μ| ≤ (K : ℝ) * ∫ x, ψ x * d x ∂μ := by
  have hweighted := lipschitz_comp_mul_integrable hψ hd hm hφ
  have hmoment : Integrable (fun x => (ψ x - a) * d x) μ := by
    apply (hm.sub (hd.const_mul a)).congr
    exact Eventually.of_forall (fun x => by dsimp; ring)
  have hbound : ∀ᵐ x ∂μ,
      ‖(φ (ψ x) - φ a) * d x‖ ≤ (K : ℝ) * ((ψ x - a) * d x) := by
    filter_upwards [hsign] with x hx
    have hlip : |φ (ψ x) - φ a| ≤ (K : ℝ) * |ψ x - a| := by
      simpa only [Real.dist_eq] using hφ.dist_le_mul (ψ x) a
    calc
      _ = |φ (ψ x) - φ a| * |d x| := by rw [norm_mul]; rfl
      _ ≤ ((K : ℝ) * |ψ x - a|) * |d x| :=
        mul_le_mul_of_nonneg_right hlip (abs_nonneg _)
      _ = (K : ℝ) * |(ψ x - a) * d x| := by rw [abs_mul]; ring
      _ = _ := by rw [abs_of_nonneg hx]
  have hcenter : (∫ x, (φ (ψ x) - φ a) * d x ∂μ) = ∫ x, φ (ψ x) * d x ∂μ := by
    calc
      _ = ∫ x, φ (ψ x) * d x - φ a * d x ∂μ := by
        apply integral_congr_ae
        exact Eventually.of_forall (fun x => by ring)
      _ = _ := by rw [integral_sub hweighted (hd.const_mul (φ a)), integral_const_mul,
        hzero, mul_zero, sub_zero]
  have h := norm_integral_le_of_norm_le (hmoment.const_mul (K : ℝ)) hbound
  rw [hcenter, Real.norm_eq_abs, integral_const_mul,
    centered_coordinate_moment_eq hd hm hzero] at h
  exact h

theorem universal_coordinate_budget_iff
    (hψ : AEMeasurable ψ μ) (hd : Integrable d μ)
    (hm : Integrable (fun x => ψ x * d x) μ)
    (hzero : (∫ x, d x ∂μ) = 0)
    (hsign : ∀ᵐ x ∂μ, 0 ≤ (ψ x - a) * d x) {B : ℝ} :
    (∀ φ : ℝ → ℝ, LipschitzWith 1 φ → |∫ x, φ (ψ x) * d x ∂μ| ≤ B) ↔
      (∫ x, ψ x * d x ∂μ) ≤ B := by
  constructor
  · intro h
    have hid := h id LipschitzWith.id
    simpa only [id_eq, abs_of_nonneg (coordinate_moment_nonneg hd hm hzero hsign)] using hid
  · intro hB φ hφ
    have h := abs_integral_comp_le_coordinate_moment hψ hd hm hzero hsign hφ
    calc
      _ ≤ ∫ x, ψ x * d x ∂μ := by simpa only [NNReal.coe_one, one_mul] using h
      _ ≤ B := hB

end CoordinateSingleCrossing
#print axioms CoordinateSingleCrossing.lipschitz_comp_mul_integrable
#print axioms CoordinateSingleCrossing.centered_coordinate_moment_eq
#print axioms CoordinateSingleCrossing.coordinate_moment_nonneg
#print axioms CoordinateSingleCrossing.abs_integral_comp_le_coordinate_moment
#print axioms CoordinateSingleCrossing.universal_coordinate_budget_iff
