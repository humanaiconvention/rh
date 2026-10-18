import RhSmoothJetLifts001
import RhCenteredPrimitiveApproximation001

/-! Private point-removal prerequisite. The actual smooth weighted lift has
an unconditional source-derivative norm bound via the native bounded energy
kernel. Variable-profile capacity is then proved from a typed uniform L2
DERIVATIVE bound. This does not assume graph convergence, but does not yet
instantiate that derivative bound for f(t)*chi(r*(t-x)). Locked public roots
are unchanged. H1 is used only for membership/control, not positivity payment.
-/
set_option maxHeartbeats 150000
noncomputable section
open Set MeasureTheory Filter
open scoped Topology ENNReal ContDiff
namespace RhSmoothKernelGraphBound
open RhAnchored RhWeightedMeasureEmbedding RhWeightedPrimitiveLift
open RhSmoothJetLifts RhTranslatedJetCapacity RhTranslatedJetDictionary

/-- Concrete finite constant from the actual positive energy kernel. -/
def graphConstant (R : ℝ) : ℝ := 4 * R^2 + 2 * R * RhNativeArchKernel.bound

lemma graphConstant_nonnegative {R : ℝ} (hR : 0 < R) : 0 ≤ graphConstant R := by
  unfold graphConstant
  positivity [RhNativeArchKernel.bound_nonnegative]

/-- Actual native weighted norm of an arbitrary physical anchored primitive. -/
theorem actualPrimitiveLift_norm_square_bound {R : ℝ} (hR : 0 < R)
    (v : ℝ → ℝ) (hv : MemLp v 2 (physicalMeasure R)) :
    ‖actualPrimitiveLift hR v hv‖^2 ≤
      graphConstant R * (∫ t in interval R, (v t)^2) := by
  rw [actualPrimitiveLift_norm_square, RhNativeArchKernel.full_energy_identity hR hv,
    ENNReal.toReal_ofReal (RhNativeArchKernel.kernel_quadratic_nonnegative hR hv)]
  have hm := RhPrimitiveApproximation.primitive_square_bound hR hv
  have he := RhCenteredPrimitiveApproximation.energy_l2_bound hR hv
  change _ + kernelQuadratic R RhNativeArchKernel.energyKernel v ≤ _
  change kernelQuadratic R RhNativeArchKernel.energyKernel v ≤ _ at he
  calc
    _ ≤ 4 * R^2 * (∫ t in interval R, (v t)^2) +
        (2 * R * RhNativeArchKernel.bound) * (∫ t in interval R, (v t)^2) :=
      add_le_add hm he
    _ = _ := by unfold graphConstant; ring

/-- No Fourier-derivative transfer is imported: the exact native physical
kernel identity controls this genuine smooth lift via its actual derivative. -/
theorem smoothLift_norm_square_bound {R : ℝ} (hR : 0 < R)
    (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) :
    ‖smoothLift hR f hf‖^2 ≤
      graphConstant R * (∫ t in interval R, (deriv f t)^2) :=
  actualPrimitiveLift_norm_square_bound hR (deriv f)
    (RhSmoothDerivativeDictionary.derivative_memLp hf)

/-- Variable profiles, not merely one fixed jet profile. Their graph bound
is explicit here; the next theorem derives it from source derivatives. -/
theorem variable_profile_capacity {R : ℝ} (j : ℕ) (F : ℕ → WeightedSpace)
    (hF : ∀ n, F n ∈ supportedSubspace R) (x : ℝ) {B : ℝ}
    (hB : ∀ n, ‖F n‖^2 ≤ B) :
    Tendsto (fun n => ‖jetVector j (F n) (hF n) x n‖) atTop (𝓝 0) := by
  have hsq : Tendsto (fun n => ‖jetVector j (F n) (hF n) x n‖^2)
      atTop (𝓝 (0 : ℝ)) := by
    have hc (n : ℕ) : 0 ≤ (1 + 5 * Real.log (scale n)) / scale n := by
      have hl := Real.log_nonneg (scale_ge_one n)
      exact div_nonneg (by linarith) (scale_pos n).le
    have hb (n : ℕ) : ‖jetVector j (F n) (hF n) x n‖^2 ≤
        ((1 + 5 * Real.log (scale n)) / scale n) * B :=
      (jetVector_uniform_square_le j (F n) (hF n) x n).trans
        (mul_le_mul_of_nonneg_left (hB n) (hc n))
    have ht := logarithmic_capacity_tendsto.mul_const B
    apply squeeze_zero (fun n => sq_nonneg _) hb
    simpa only [zero_mul] using ht
  have h := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using h

/-- A genuinely proved capacity conclusion from a uniform actual derivative
square integral. No final cutoff-product estimate is claimed until hD is
proved for that explicit family. -/
theorem variable_smooth_capacity {R : ℝ} (hR : 0 < R)
    (phi : ℕ → ℝ → ℝ) (hf : ∀ n, ContDiff ℝ ∞ (phi n))
    (x : ℝ) {M : ℝ}
    (hD : ∀ n, (∫ t in interval R, (deriv (phi n) t)^2) ≤ M) :
    Tendsto (fun n => ‖jetVector 0 (smoothLift hR (phi n) (hf n))
      (smoothLift_supported hR (phi n) (hf n)) x n‖) atTop (𝓝 0) := by
  apply variable_profile_capacity 0
  intro n
  exact (smoothLift_norm_square_bound hR (phi n) (hf n)).trans
    (mul_le_mul_of_nonneg_left (hD n) (graphConstant_nonnegative hR))

/-- Literal spatial representatives stay AE; their pointwise values are not
assigned to arbitrary elements of the L2 quotient. -/
theorem variable_smooth_physical_ae {R : ℝ} (hR : 0 < R)
    (phi : ℕ → ℝ → ℝ) (hf : ∀ n, ContDiff ℝ ∞ (phi n))
    (hs : ∀ n, tsupport (phi n) ⊆ Ioo (-R) R) (x : ℝ) (n : ℕ) :
    physicalEmbedding (jetVector 0 (smoothLift hR (phi n) (hf n))
      (smoothLift_supported hR (phi n) (hf n)) x n) =ᵐ[volume]
      fun t => (phi n ((t-x)*scale n) : ℂ) := by
  have h := jetVector_physical_ae 0 (smoothLift hR (phi n) (hf n))
    (smoothLift_supported hR (phi n) (hf n)) x n (fun t => (phi n t : ℂ))
    (smoothLift_physical hR (phi n) (hf n) (hs n))
  simpa using h

/-- The rescaled modulated profile is EXACTLY the actual cutoff-product. -/
lemma modulated_profile_identity (f chi : ℝ → ℝ) (x t : ℝ) (n : ℕ) :
    (fun u => f (x + u / scale n) * chi u) ((t-x)*scale n) =
      f t * chi ((t-x)*scale n) := by
  have hs : scale n ≠ 0 := (scale_pos n).ne'
  have he : x + ((t-x)*scale n) / scale n = t := by field_simp; ring
  dsimp only
  rw [he]

end RhSmoothKernelGraphBound
#print axioms RhSmoothKernelGraphBound.actualPrimitiveLift_norm_square_bound
#print axioms RhSmoothKernelGraphBound.smoothLift_norm_square_bound
#print axioms RhSmoothKernelGraphBound.variable_profile_capacity
#print axioms RhSmoothKernelGraphBound.variable_smooth_capacity
#print axioms RhSmoothKernelGraphBound.variable_smooth_physical_ae
#print axioms RhSmoothKernelGraphBound.modulated_profile_identity
