import RhInteriorSmoothSequence001
import RhCenteredSmoothPrimitive001
import RhPhysicalPrimitiveCongruence001

/-! Actual complete-form smooth approximation for the real physical primitive
class. All convergence is constructed from ordinary physical L2 density and
the native anchor capacity calculation, not assumed as a form premise. -/
noncomputable section
open Set MeasureTheory Filter FourierTransform
open scoped Topology ContDiff BigOperators ENNReal
namespace RhActualSmoothFormClosure
open RhAnchored RhAllPrime RhTail RhCompleteFormBound
open RhCenteredPrimitiveApproximation RhCenteredSmoothPrimitive
open RhPhysicalPrimitiveCongruence RhActualCoreBump

/-- A literal error function in primitive coordinates. -/
def approximationError (R : ℝ) (f : ℕ → ℝ → ℝ) (v : ℝ → ℝ) (n : ℕ) : ℝ → ℝ :=
  f n - primitive R v

/-- This value is used below only after actual full-energy finiteness is proved. -/
def graphValue (R : ℝ) (w : ℝ → ℝ) (hw : MemLp w 2 (physicalMeasure R)) : ℝ :=
  (fullFrequencyEnergy (1 / 2) (physicalFourierVector R w hw)).toReal + mass R w

/-- Entire native shifted complete value: both ranks and every radius-cutoff
prime-power two-delay term remain inside boundedPart with their actual signs. -/
def shiftedCompleteValue (R : ℝ) (w : ℝ → ℝ)
    (hw : MemLp w 2 (physicalMeasure R)) : ℝ :=
  (fullFrequencyEnergy (1 / 2) (physicalFourierVector R w hw)).toReal +
    boundedPart R archConstant (radiusCutoff R) w +
    (boundConstant R archConstant (radiusCutoff R) + 1) * mass R w

lemma shiftedCompleteValue_bounds {R : ℝ} {w : ℝ → ℝ}
    (hw : MemLp w 2 (physicalMeasure R)) :
    0 ≤ shiftedCompleteValue R w hw ∧
      shiftedCompleteValue R w hw ≤
        (2 * boundConstant R archConstant (radiusCutoff R) + 1) * graphValue R w hw := by
  have hb := complete_boundedPart_abs_bound hw archConstant (radiusCutoff R)
  have hlo := (abs_le.mp hb).1
  have hup := (abs_le.mp hb).2
  have hN := mass_nonneg R w
  have hK := boundConstant_nonneg R archConstant (radiusCutoff R)
  have hE : 0 ≤ (fullFrequencyEnergy (1 / 2) (physicalFourierVector R w hw)).toReal :=
    ENNReal.toReal_nonneg
  unfold shiftedCompleteValue graphValue
  constructor <;> nlinarith [mul_nonneg hK hE]

/-- Constructed smooth compact approximants to every actual anchored primitive.
The graph and shifted complete errors use the literal smooth-minus-primitive
function, identified through actual restricted-AE and toLp congruence. -/
theorem actual_smooth_complete_form_approximation {R : ℝ} (hR : 0 < R)
    {v : ℝ → ℝ} (hv : MemLp v 2 (physicalMeasure R)) :
    ∃ f : ℕ → ℝ → ℝ,
      (∀ n, ContDiff ℝ ∞ (f n)) ∧ (∀ n, HasCompactSupport (f n)) ∧
      (∀ n, tsupport (f n) ⊆ Ioo (-R) R) ∧
      (∀ n, approximationError R f v n =ᵐ[physicalMeasure R]
        primitive R (deriv (f n) - v)) ∧
      ∃ hf : ∀ n, MemLp (approximationError R f v n) 2 (physicalMeasure R),
        (∀ n, fullFrequencyEnergy (1 / 2)
          (physicalFourierVector R (approximationError R f v n) (hf n)) < ⊤) ∧
        Tendsto (fun n => graphValue R (approximationError R f v n) (hf n)) atTop (𝓝 0) ∧
        Tendsto (fun n => shiftedCompleteValue R (approximationError R f v n) (hf n))
          atTop (𝓝 0) := by
  obtain ⟨u, huS, huC, huT, hu, hu0⟩ :=
    RhInteriorSmoothSequence.exists_interior_smooth_sequence hR hv
  let M : ℕ → ℝ := fun n => totalMass R (u n)
  let phi : ℕ → ContDiffBump (0 : ℝ) := centralBump R hR
  let e : ℕ → ℝ → ℝ := fun n => u n - v
  have he (n : ℕ) : MemLp (e n) 2 (physicalMeasure R) := (hu n).sub hv
  have he0 : Tendsto (fun n => ∫ t in interval R, (e n t)^2) atTop (𝓝 0) := hu0
  have hM : Tendsto M atTop (𝓝 (totalMass R v)) :=
    RhPhysicalMassConvergence.totalMass_tendsto_of_l2_error hR u v hu hv hu0
  have hphi : Tendsto (fun n => (phi n).rOut) atTop (𝓝 0) := rOut_tendsto R hR
  have hd (n : ℕ) : MemLp (centeredSource e M phi n) 2 (physicalMeasure R) :=
    RhCenteredPrimitiveApproximation.centered_memLp e M phi he n
  have hCG := centered_graph_error_tendsto_zero hR e M phi he he0 hM hphi
  obtain ⟨f, hfS, hfC, hfT, hfD, hfA⟩ :=
    exists_centered_smooth_primitives hR u huS huC huT hu
  have hsource (n : ℕ) : centeredSource e M phi n = centeredPhysical R hR u n - v := by
    funext t
    simp only [centeredSource, centeredPhysical, e, M, phi,
      Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hprimitive (n : ℕ) : primitive R (centeredSource e M phi n) =
      primitive R (centeredPhysical R hR u n) - primitive R v := by
    rw [hsource n]
    simpa only [one_smul] using primitive_difference
      (RhCenteredSmoothPrimitive.centered_memLp hR u hu n) hv 1
  have hAE (n : ℕ) : approximationError R f v n =ᵐ[physicalMeasure R]
      primitive R (centeredSource e M phi n) := by
    filter_upwards [ae_restrict_of_ae (hfA n), ae_restrict_mem measurableSet_Icc]
      with t hft ht
    rw [zeroExtension_eq ht] at hft
    change f n t - primitive R v t = primitive R (centeredSource e M phi n) t
    rw [hft, hprimitive n]
    rfl
  have hderiv (n : ℕ) : deriv (f n) - v = centeredSource e M phi n := by
    rw [hfD n, hsource n]
  have hError (n : ℕ) : MemLp (approximationError R f v n) 2 (physicalMeasure R) :=
    (RhDilationRank.continuous_memLp (hfS n).continuous).sub (primitive_memLp hv)
  have hFinite (n : ℕ) : fullFrequencyEnergy (1 / 2)
      (physicalFourierVector R (approximationError R f v n) (hError n)) < ⊤ := by
    rw [fullFrequencyEnergy_congr_ae (hError n) (primitive_memLp (hd n)) (hAE n) (1 / 2)]
    exact RhPrimitiveFormDomain.physical_primitive_full_arch_finite hR (hd n)
  have hGraphEq (n : ℕ) : graphValue R (approximationError R f v n) (hError n) =
      energy R (centeredSource e M phi n) + primitiveMass R (centeredSource e M phi n) := by
    unfold graphValue mass
    rw [fullFrequencyEnergy_congr_ae (hError n) (primitive_memLp (hd n)) (hAE n) (1 / 2),
      RhNativeArchKernel.full_energy_identity hR (hd n),
      ENNReal.toReal_ofReal (RhNativeArchKernel.kernel_quadratic_nonnegative hR (hd n)),
      square_mass_congr_ae (hAE n)]
  have hGraph : Tendsto (fun n => graphValue R (approximationError R f v n) (hError n))
      atTop (𝓝 0) := by
    simp_rw [hGraphEq]
    exact hCG
  have hShift : Tendsto (fun n => shiftedCompleteValue R (approximationError R f v n) (hError n))
      atTop (𝓝 0) := by
    apply squeeze_zero' (g := fun n =>
      (2 * boundConstant R archConstant (radiusCutoff R) + 1) *
        graphValue R (approximationError R f v n) (hError n))
      (Eventually.of_forall (fun n => (shiftedCompleteValue_bounds (hError n)).1))
    · exact Eventually.of_forall (fun n => (shiftedCompleteValue_bounds (hError n)).2)
    · simpa only [mul_zero] using hGraph.const_mul
        (2 * boundConstant R archConstant (radiusCutoff R) + 1)
  refine ⟨f, hfS, hfC, hfT, ?_, hError, hFinite, hGraph, hShift⟩
  intro n
  rw [hderiv n]
  exact hAE n

end RhActualSmoothFormClosure
#print axioms RhActualSmoothFormClosure.shiftedCompleteValue_bounds
#print axioms RhActualSmoothFormClosure.actual_smooth_complete_form_approximation
