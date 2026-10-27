import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import JensenPointwise
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.Tactic.FunProp

/-! UNCOMPILED bounded preparation only. New Gaussian helpers are inline;
accepted JensenPointwise and its JensenWeights dependency must be imported
from existing authenticated objects. No measure theorem is accepted yet. -/


/-!
# Gaussian domination for the signed-measure Jensen preparation

UNCOMPILED proof-script proposal. No acceptance, compiler execution,
admission check or actual axiom output is asserted by this file.

All scalar inequalities are unconditional apart from their displayed
real-variable hypotheses. The exact factor `8` gives `8 / 24 = 1 / 3`
when the accepted pointwise Jensen estimate is integrated.
-/

noncomputable section

namespace SignedJensenGaussianPrep

/-- For a nonnegative real argument, the two exponential summands defining
`cosh` are both bounded by the positive exponential. -/
theorem cosh_le_exp_nonneg {x : ℝ} (hx : 0 ≤ x) :
    Real.cosh x ≤ Real.exp x := by
  have hneg : Real.exp (-x) ≤ Real.exp x :=
    Real.exp_le_exp.mpr (by linarith)
  rw [Real.cosh_eq]
  linarith

/-- Exact Young inequality in the parameterization used by the Gaussian
moment assumption. No square root of `b` is introduced. -/
theorem sqrt_mul_le_gaussian_split {b r u : ℝ}
    (hb : 0 < b) (hr : 0 ≤ r) :
    Real.sqrt r * u ≤ r / (2 * b) + b * u ^ 2 / 2 := by
  have hsqrt : (Real.sqrt r) ^ 2 = r := Real.sq_sqrt hr
  have hsq := sq_nonneg (b * u - Real.sqrt r)
  have hden : 0 < 2 * b := by positivity
  have heq : r / (2 * b) + b * u ^ 2 / 2 =
      (r + b ^ 2 * u ^ 2) / (2 * b) := by
    field_simp [ne_of_gt hb]
    <;> ring
  rw [heq]
  apply (le_div_iff₀ hden).2
  nlinarith [hsqrt, hsq]

/-- Half of the Gaussian exponent pays for the hyperbolic factor. -/
theorem cosh_gaussian_half {b r u : ℝ}
    (hb : 0 < b) (hr : 0 ≤ r) (hu : 0 ≤ u) :
    Real.cosh (Real.sqrt r * u) ≤
      Real.exp (r / (2 * b)) * Real.exp (b * u ^ 2 / 2) := by
  calc
    Real.cosh (Real.sqrt r * u) ≤ Real.exp (Real.sqrt r * u) :=
      cosh_le_exp_nonneg (mul_nonneg (Real.sqrt_nonneg r) hu)
    _ ≤ Real.exp (r / (2 * b) + b * u ^ 2 / 2) :=
      Real.exp_le_exp.mpr (sqrt_mul_le_gaussian_split hb hr)
    _ = Real.exp (r / (2 * b)) * Real.exp (b * u ^ 2 / 2) :=
      Real.exp_add _ _

/-- The second exponential-series term gives the exact elementary
polynomial payment `u^4 ≤ (8/b^2) exp(b u^2/2)`. -/
theorem fourth_gaussian_half {b : ℝ} (hb : 0 < b) (u : ℝ) :
    u ^ 4 ≤ (8 / b ^ 2) * Real.exp (b * u ^ 2 / 2) := by
  have hx : 0 ≤ b * u ^ 2 / 2 := by positivity
  have hterm := Real.pow_div_factorial_le_exp (b * u ^ 2 / 2) hx 2
  norm_num [Nat.factorial] at hterm
  have hpoly : b ^ 2 * u ^ 4 / 8 ≤ Real.exp (b * u ^ 2 / 2) := by
    nlinarith [hterm]
  have heq : (8 / b ^ 2) * Real.exp (b * u ^ 2 / 2) =
      (8 * Real.exp (b * u ^ 2 / 2)) / b ^ 2 := by ring
  rw [heq]
  apply (le_div_iff₀ (sq_pos_of_pos hb)).2
  nlinarith [hpoly]

/-- The full exact integrable majorant used for the `1/24` pointwise
remainder. Its coefficient is `8`, not an unspecified constant. -/
theorem fourth_cosh_gaussian {b r u : ℝ}
    (hb : 0 < b) (hr : 0 ≤ r) (hu : 0 ≤ u) :
    u ^ 4 * Real.cosh (Real.sqrt r * u) ≤
      ((8 / b ^ 2) * Real.exp (r / (2 * b))) * Real.exp (b * u ^ 2) := by
  have hpoly := fourth_gaussian_half hb u
  have hcosh := cosh_gaussian_half hb hr hu
  have he : Real.exp (b * u ^ 2 / 2) * Real.exp (b * u ^ 2 / 2) =
      Real.exp (b * u ^ 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    u ^ 4 * Real.cosh (Real.sqrt r * u) ≤
        ((8 / b ^ 2) * Real.exp (b * u ^ 2 / 2)) *
          (Real.exp (r / (2 * b)) * Real.exp (b * u ^ 2 / 2)) :=
      mul_le_mul hpoly hcosh (Real.cosh_pos _).le (by positivity)
    _ = ((8 / b ^ 2) * Real.exp (r / (2 * b))) *
        (Real.exp (b * u ^ 2 / 2) * Real.exp (b * u ^ 2 / 2)) := by ring
    _ = ((8 / b ^ 2) * Real.exp (r / (2 * b))) *
        Real.exp (b * u ^ 2) := by rw [he]

/-- An economical majorant for the unweighted complete kernel. This is
separate from the fourth-moment error majorant and does not alter it. -/
theorem cosh_gaussian_full {b r u : ℝ}
    (hb : 0 < b) (hr : 0 ≤ r) (hu : 0 ≤ u) :
    Real.cosh (Real.sqrt r * u) ≤
      Real.exp (r / (4 * b)) * Real.exp (b * u ^ 2) := by
  have h := cosh_gaussian_half (b := 2 * b) (by positivity) hr hu
  have he1 : r / (2 * (2 * b)) = r / (4 * b) := by ring
  have he2 : (2 * b) * u ^ 2 / 2 = b * u ^ 2 := by ring
  simpa only [he1, he2] using h

/-- Scalar bridge retaining exactly the downstream coefficient `1/3`.
The degree is real here; the measure wrapper supplies the positive natural
degree cast, without silently changing normalization. -/
theorem pointwise_error_gaussian {b d r u : ℝ}
    (hb : 0 < b) (hd : 0 < d) (hr : 0 ≤ r) (hu : 0 ≤ u) :
    (r ^ 2 * u ^ 4 / (24 * d)) * Real.cosh (Real.sqrt r * u) ≤
      ((r ^ 2 / (3 * b ^ 2 * d)) * Real.exp (r / (2 * b))) *
        Real.exp (b * u ^ 2) := by
  have h := mul_le_mul_of_nonneg_left (fourth_cosh_gaussian hb hr hu)
    (show 0 ≤ r ^ 2 / (24 * d) by positivity)
  have he1 : (r ^ 2 / (24 * d)) * (u ^ 4 * Real.cosh (Real.sqrt r * u)) =
      (r ^ 2 * u ^ 4 / (24 * d)) * Real.cosh (Real.sqrt r * u) := by ring
  have he2 : (r ^ 2 / (24 * d)) *
      (((8 / b ^ 2) * Real.exp (r / (2 * b))) * Real.exp (b * u ^ 2)) =
      ((r ^ 2 / (3 * b ^ 2 * d)) * Real.exp (r / (2 * b))) *
        Real.exp (b * u ^ 2) := by
    field_simp [ne_of_gt hb, ne_of_gt hd]
    <;> ring
  rw [he1, he2] at h
  exact h

end SignedJensenGaussianPrep

-- Requested audits, not actual reports: this draft has not been compiled.
#print axioms SignedJensenGaussianPrep.cosh_gaussian_half
#print axioms SignedJensenGaussianPrep.fourth_gaussian_half
#print axioms SignedJensenGaussianPrep.fourth_cosh_gaussian
#print axioms SignedJensenGaussianPrep.cosh_gaussian_full
#print axioms SignedJensenGaussianPrep.pointwise_error_gaussian


/-! UNCOMPILED preparation only. Actual kernel integrals against positive
measures and a difference of positive measures; no Jordan identification,
series/integral interchange, entire transform, or actual-source theorem. -/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace SignedJensenMeasurePrep

abbrev U := {u : ℝ // 0 ≤ u}

def gaussian (b : ℝ) (u : U) : ℝ := Real.exp (b * (u : ℝ) ^ 2)

def nativeKernel (z : ℂ) (u : U) : ℂ :=
  SignedJensenKernelPrep.completeKernel (z * (u : ℂ) ^ 2)

def finiteNativeKernel (d : ℕ) (z : ℂ) (u : U) : ℂ :=
  SignedJensenKernelPrep.finiteKernel d (z * (u : ℂ) ^ 2)

def fourthCosh (r : ℝ) (u : U) : ℝ :=
  (u : ℝ) ^ 4 * Real.cosh (Real.sqrt r * (u : ℝ))

def signedPair (μp μm : Measure U) (f : U → ℂ) : ℂ :=
  (∫ u, f u ∂μp) - (∫ u, f u ∂μm)

/-- Nonnegativity, not strict positivity: the zero measure is allowed. -/
theorem gaussian_mass_nonneg (μ : Measure U) (b : ℝ) :
    0 ≤ ∫ u, gaussian b u ∂μ :=
  integral_nonneg (fun u => (Real.exp_pos (b * (u : ℝ) ^ 2)).le)
theorem measurable_kernelTerm (z : ℂ) (j : ℕ) :
    Measurable (fun u : U =>
      SignedJensenKernelPrep.kernelTerm (z * (u : ℂ) ^ 2) j) := by
  unfold SignedJensenKernelPrep.kernelTerm
  fun_prop

/-- A pointwise limit of genuine finite partial sums. No measurable-tsum
fallback or second-countability instance for the target is needed here. -/
theorem stronglyMeasurable_nativeKernel (z : ℂ) :
    StronglyMeasurable (nativeKernel z) := by
  apply stronglyMeasurable_of_tendsto Filter.atTop
    (f := fun n : ℕ => fun u : U =>
      ∑ j ∈ Finset.range n,
        SignedJensenKernelPrep.kernelTerm (z * (u : ℂ) ^ 2) j)
  · intro n
    apply Continuous.stronglyMeasurable
    unfold SignedJensenKernelPrep.kernelTerm
    fun_prop
  · apply tendsto_pi_nhds.mpr
    intro u
    have ha : ‖z * (u : ℂ) ^ 2‖ ≤
        (Real.sqrt ‖z * (u : ℂ) ^ 2‖) ^ 2 := by
      rw [Real.sq_sqrt (norm_nonneg _)]
    exact (SignedJensenKernelPrep.kernel_summable _ _ ha).hasSum.tendsto_sum_nat

theorem measurable_nativeKernel (z : ℂ) : Measurable (nativeKernel z) :=
  (stronglyMeasurable_nativeKernel z).measurable

theorem stronglyMeasurable_finiteNativeKernel (d : ℕ) (z : ℂ) :
    StronglyMeasurable (finiteNativeKernel d z) := by
  apply Continuous.stronglyMeasurable
  unfold finiteNativeKernel SignedJensenKernelPrep.finiteKernel
    SignedJensenKernelPrep.kernelTerm
  fun_prop

theorem measurable_finiteNativeKernel (d : ℕ) (z : ℂ) :
    Measurable (finiteNativeKernel d z) :=
  (stronglyMeasurable_finiteNativeKernel d z).measurable

theorem nativeKernel_norm_le (z : ℂ) (r : ℝ)
    (hr : 0 ≤ r) (hz : ‖z‖ ≤ r) (u : U) :
    ‖nativeKernel z u‖ ≤ Real.cosh (Real.sqrt r * (u : ℝ)) := by
  have ha : ‖z * (u : ℂ) ^ 2‖ ≤ (Real.sqrt r * (u : ℝ)) ^ 2 := by
    rw [norm_mul, norm_pow, Complex.norm_of_nonneg u.property]
    calc
      ‖z‖ * (u : ℝ) ^ 2 ≤ r * (u : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_right hz (sq_nonneg _)
      _ = (Real.sqrt r * (u : ℝ)) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt hr]
  exact (SignedJensenKernelPrep.kernel_summable _ _ ha).hasSum.norm_le_of_bounded
    (Real.hasSum_cosh (Real.sqrt r * (u : ℝ)))
    (fun j => SignedJensenKernelPrep.kernelTerm_norm_le _ _ ha j)

theorem integrable_nativeKernel (μ : Measure U) (b r : ℝ) (z : ℂ)
    (hb : 0 < b) (hr : 0 ≤ r) (hz : ‖z‖ ≤ r)
    (hG : Integrable (gaussian b) μ) : Integrable (nativeKernel z) μ := by
  apply (hG.const_mul (Real.exp (r / (4 * b)))).mono'
    (stronglyMeasurable_nativeKernel z).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun u =>
    (nativeKernel_norm_le z r hr hz u).trans
      (SignedJensenGaussianPrep.cosh_gaussian_full hb hr u.property)

theorem integrable_fourthCosh (μ : Measure U) (b r : ℝ)
    (hb : 0 < b) (hr : 0 ≤ r)
    (hG : Integrable (gaussian b) μ) : Integrable (fourthCosh r) μ := by
  apply (hG.const_mul ((8 / b ^ 2) * Real.exp (r / (2 * b)))).mono'
    (by unfold fourthCosh; fun_prop)
  apply Filter.Eventually.of_forall
  intro u
  have hn : 0 ≤ fourthCosh r u :=
    mul_nonneg (pow_nonneg u.property _) (le_of_lt (Real.cosh_pos _))
  rw [Real.norm_eq_abs, abs_of_nonneg hn]
  exact SignedJensenGaussianPrep.fourth_cosh_gaussian hb hr u.property

theorem integrable_kernelError (μ : Measure U) (b r : ℝ) (z : ℂ) (d : ℕ)
    (hb : 0 < b) (hr : 0 ≤ r) (hz : ‖z‖ ≤ r) (hd : 1 ≤ d)
    (hG : Integrable (gaussian b) μ) :
    Integrable (fun u => finiteNativeKernel d z u - nativeKernel z u) μ := by
  have h4 := integrable_fourthCosh μ b r hb hr hG
  apply (h4.const_mul (r ^ 2 / (24 * (d : ℝ)))).mono'
    ((stronglyMeasurable_finiteNativeKernel d z).sub
      (stronglyMeasurable_nativeKernel z)).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro u
  have h := SignedJensenKernelPrep.pointwise_kernel_disk d hd z (u : ℝ) r
    u.property hr hz
  dsimp [finiteNativeKernel, nativeKernel, fourthCosh]
  convert h using 1 <;> ring

theorem integrable_finiteNativeKernel (μ : Measure U) (b r : ℝ) (z : ℂ) (d : ℕ)
    (hb : 0 < b) (hr : 0 ≤ r) (hz : ‖z‖ ≤ r) (hd : 1 ≤ d)
    (hG : Integrable (gaussian b) μ) : Integrable (finiteNativeKernel d z) μ := by
  have he := integrable_kernelError μ b r z d hb hr hz hd hG
  have hc := integrable_nativeKernel μ b r z hb hr hz hG
  convert he.add hc using 1
  funext u
  change finiteNativeKernel d z u =
    (finiteNativeKernel d z u - nativeKernel z u) + nativeKernel z u
  ring

/-- All integrability is established before norm-integral comparison. -/
theorem signedPair_difference_bound (μp μm : Measure U)
    (f g : U → ℂ) (a : U → ℝ)
    (hf : Integrable f (μp + μm)) (hg : Integrable g (μp + μm))
    (ha : Integrable a (μp + μm)) (hbound : ∀ u, ‖f u - g u‖ ≤ a u) :
    ‖signedPair μp μm f - signedPair μp μm g‖ ≤ ∫ u, a u ∂(μp + μm) := by
  have hfP := hf.left_of_add_measure
  have hfM := hf.right_of_add_measure
  have hgP := hg.left_of_add_measure
  have hgM := hg.right_of_add_measure
  have heP : Integrable (fun u => f u - g u) μp := hfP.sub hgP
  have heM : Integrable (fun u => f u - g u) μm := hfM.sub hgM
  have haP := ha.left_of_add_measure
  have haM := ha.right_of_add_measure
  have hP := norm_integral_le_of_norm_le haP (Filter.Eventually.of_forall hbound)
  have hM := norm_integral_le_of_norm_le haM (Filter.Eventually.of_forall hbound)
  calc
    ‖signedPair μp μm f - signedPair μp μm g‖ =
        ‖(∫ u, f u - g u ∂μp) - (∫ u, f u - g u ∂μm)‖ := by
      rw [integral_sub hfP hgP, integral_sub hfM hgM]
      congr 1
      unfold signedPair
      ring
    _ ≤ ‖∫ u, f u - g u ∂μp‖ + ‖∫ u, f u - g u ∂μm‖ := norm_sub_le _ _
    _ ≤ (∫ u, a u ∂μp) + (∫ u, a u ∂μm) := add_le_add hP hM
    _ = ∫ u, a u ∂(μp + μm) := (integral_add_measure haP haM).symm

theorem signedPair_kernel_error (μp μm : Measure U) (b r : ℝ) (z : ℂ) (d : ℕ)
    (hb : 0 < b) (hr : 0 ≤ r) (hz : ‖z‖ ≤ r) (hd : 1 ≤ d)
    (hG : Integrable (gaussian b) (μp + μm)) :
    ‖signedPair μp μm (finiteNativeKernel d z) - signedPair μp μm (nativeKernel z)‖ ≤
      (r ^ 2 / (24 * (d : ℝ))) * (∫ u, fourthCosh r u ∂(μp + μm)) := by
  have hf := integrable_finiteNativeKernel (μp + μm) b r z d hb hr hz hd hG
  have hc := integrable_nativeKernel (μp + μm) b r z hb hr hz hG
  have h4 := integrable_fourthCosh (μp + μm) b r hb hr hG
  have hbnd : ∀ u : U,
      ‖finiteNativeKernel d z u - nativeKernel z u‖ ≤
        (r ^ 2 / (24 * (d : ℝ))) * fourthCosh r u := by
    intro u
    have h := SignedJensenKernelPrep.pointwise_kernel_disk d hd z (u : ℝ) r
      u.property hr hz
    dsimp [finiteNativeKernel, nativeKernel, fourthCosh]
    convert h using 1 <;> ring
  simpa only [integral_const_mul] using
    signedPair_difference_bound μp μm _ _ _ hf hc
      (h4.const_mul (r ^ 2 / (24 * (d : ℝ)))) hbnd

theorem signedPair_kernel_error_gaussian (μp μm : Measure U)
    (b r : ℝ) (z : ℂ) (d : ℕ)
    (hb : 0 < b) (hr : 0 ≤ r) (hz : ‖z‖ ≤ r) (hd : 1 ≤ d)
    (hG : Integrable (gaussian b) (μp + μm)) :
    ‖signedPair μp μm (finiteNativeKernel d z) - signedPair μp μm (nativeKernel z)‖ ≤
      ((r ^ 2 / (3 * b ^ 2 * (d : ℝ))) * Real.exp (r / (2 * b))) *
        (∫ u, gaussian b u ∂(μp + μm)) := by
  have hdpos : (0 : ℝ) < (d : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hd)
  have hf := integrable_finiteNativeKernel (μp + μm) b r z d hb hr hz hd hG
  have hc := integrable_nativeKernel (μp + μm) b r z hb hr hz hG
  have hbnd : ∀ u : U,
      ‖finiteNativeKernel d z u - nativeKernel z u‖ ≤
        ((r ^ 2 / (3 * b ^ 2 * (d : ℝ))) * Real.exp (r / (2 * b))) * gaussian b u := by
    intro u
    exact (SignedJensenKernelPrep.pointwise_kernel_disk d hd z (u : ℝ) r
      u.property hr hz).trans
        (SignedJensenGaussianPrep.pointwise_error_gaussian hb hdpos hr u.property)
  simpa only [integral_const_mul] using
    signedPair_difference_bound μp μm _ _ _ hf hc
      (hG.const_mul ((r ^ 2 / (3 * b ^ 2 * (d : ℝ))) * Real.exp (r / (2 * b)))) hbnd

end SignedJensenMeasurePrep

#print axioms SignedJensenMeasurePrep.gaussian_mass_nonneg
#print axioms SignedJensenMeasurePrep.measurable_nativeKernel
#print axioms SignedJensenMeasurePrep.nativeKernel_norm_le
#print axioms SignedJensenMeasurePrep.integrable_nativeKernel
#print axioms SignedJensenMeasurePrep.integrable_fourthCosh
#print axioms SignedJensenMeasurePrep.integrable_kernelError
#print axioms SignedJensenMeasurePrep.integrable_finiteNativeKernel
#print axioms SignedJensenMeasurePrep.signedPair_difference_bound
#print axioms SignedJensenMeasurePrep.signedPair_kernel_error
#print axioms SignedJensenMeasurePrep.signedPair_kernel_error_gaussian



