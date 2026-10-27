import JensenEvenMoments
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Analysis.Complex.LocallyUniformLimit

/-! UNCOMPILED bounded preparation. No new theorem or axiom report is
accepted. The interchange helpers are inline; accepted provider objects
must be reused from their existing authenticated directories. -/


/-!
# Infinite moment dictionary: uncompiled preparation

This complete proposed script has NOT been checked by Lean. No compiler or
admission check is authorized by preparing it. Every interchange below is
supported by a summable series of genuine Bochner integrals of norms.
Positive measures remain an explicit pair, not an asserted Jordan pair.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace SignedJensenEntirePrep

open SignedJensenMeasurePrep SignedJensenMomentsPrep

def seriesTerm (z : ℂ) (u : U) (j : ℕ) : ℂ :=
  SignedJensenKernelPrep.kernelTerm (z * (u : ℂ) ^ 2) j

def momentCoefficient (μp μm : Measure U) (j : ℕ) : ℂ :=
  (-1 : ℂ) ^ j * (signedMoment μp μm j : ℂ) / ((2 * j).factorial : ℂ)

def momentTransform (μp μm : Measure U) (z : ℂ) : ℂ :=
  ∑' j : ℕ, momentCoefficient μp μm j * z ^ j

/-- The exact exponential majorant. The radius is nonnegative in its uses. -/
def majorant (b r : ℝ) (j : ℕ) : ℝ :=
  (r / b) ^ j / (j.factorial : ℝ)

theorem factorial_square_le (j : ℕ) :
    (j.factorial : ℝ) * (j.factorial : ℝ) ≤ ((2 * j).factorial : ℝ) := by
  have hn : j.factorial * j.factorial ≤ (j + j).factorial :=
    Nat.le_of_dvd (Nat.factorial_pos _) (Nat.factorial_mul_factorial_dvd_factorial_add j j)
  have heq : j + j = 2 * j := by ring
  rw [heq] at hn
  exact_mod_cast hn

theorem factorial_ratio_le (j : ℕ) :
    (j.factorial : ℝ) / ((2 * j).factorial : ℝ) ≤ 1 / (j.factorial : ℝ) := by
  have hf : 0 < (j.factorial : ℝ) := by positivity
  have h2 : 0 < ((2 * j).factorial : ℝ) := by positivity
  apply (div_le_div_iff₀ h2 hf).2
  simpa only [one_mul] using factorial_square_le j

theorem majorant_nonneg (b r : ℝ) (j : ℕ) (hb : 0 < b) (hr : 0 ≤ r) :
    0 ≤ majorant b r j := by
  unfold majorant
  positivity

set_option backward.defeqAttrib.useBackward true in
theorem majorant_hasSum (b r : ℝ) :
    HasSum (majorant b r) (Real.exp (r / b)) := by
  change HasSum (fun j : ℕ => (r / b) ^ j / (j.factorial : ℝ)) (Real.exp (r / b))
  simpa only [Real.exp_eq_exp_ℝ] using
    (NormedSpace.expSeries_div_hasSum_exp (r / b))

theorem seriesTerm_eq (z : ℂ) (u : U) (j : ℕ) :
    seriesTerm z u j =
      ((-1 : ℂ) ^ j * z ^ j / ((2 * j).factorial : ℂ)) *
        (evenPower j u : ℂ) := by
  rw [seriesTerm, SignedJensenKernelPrep.kernelTerm_native]
  simp only [evenPower, Complex.ofReal_pow]
  ring

theorem seriesTerm_norm (z : ℂ) (u : U) (j : ℕ) :
    ‖seriesTerm z u j‖ =
      (‖z‖ ^ j / ((2 * j).factorial : ℝ)) * evenPower j u := by
  rw [seriesTerm, SignedJensenKernelPrep.kernelTerm_norm]
  simp only [norm_mul, norm_pow, Complex.norm_of_nonneg u.property,
    evenPower, mul_pow, ← pow_mul]
  ring

/-- Gaussian moment payment, retaining every coefficient before integration. -/
theorem seriesTerm_norm_le (z : ℂ) (u : U) (j : ℕ) (b r : ℝ)
    (hb : 0 < b) (hr : 0 ≤ r) (hz : ‖z‖ ≤ r) :
    ‖seriesTerm z u j‖ ≤ majorant b r j * gaussian b u := by
  have hp := evenPower_le_gaussian b j hb u
  have hratio := factorial_ratio_le j
  have hpow : (‖z‖ / b) ^ j ≤ (r / b) ^ j :=
    pow_le_pow_left₀ (div_nonneg (norm_nonneg _) hb.le)
      (div_le_div_of_nonneg_right hz hb.le) j
  have hcoeff : (‖z‖ ^ j / ((2 * j).factorial : ℝ)) *
      ((j.factorial : ℝ) / b ^ j) ≤ majorant b r j := by
    calc
      (‖z‖ ^ j / ((2 * j).factorial : ℝ)) *
          ((j.factorial : ℝ) / b ^ j) =
          (‖z‖ / b) ^ j * ((j.factorial : ℝ) / ((2 * j).factorial : ℝ)) := by
        rw [div_pow]
        ring
      _ ≤ (r / b) ^ j * (1 / (j.factorial : ℝ)) :=
        mul_le_mul hpow hratio (by positivity) (by positivity)
      _ = majorant b r j := by unfold majorant; ring
  rw [seriesTerm_norm]
  calc
    (‖z‖ ^ j / ((2 * j).factorial : ℝ)) * evenPower j u ≤
        (‖z‖ ^ j / ((2 * j).factorial : ℝ)) *
          (((j.factorial : ℝ) / b ^ j) * gaussian b u) :=
      mul_le_mul_of_nonneg_left hp (by positivity)
    _ = ((‖z‖ ^ j / ((2 * j).factorial : ℝ)) *
        ((j.factorial : ℝ) / b ^ j)) * gaussian b u := by ring
    _ ≤ majorant b r j * gaussian b u :=
      mul_le_mul_of_nonneg_right hcoeff (Real.exp_pos _).le

theorem integrable_seriesTerm (μ : Measure U) (b : ℝ) (z : ℂ) (j : ℕ)
    (hb : 0 < b) (hG : Integrable (gaussian b) μ) :
    Integrable (fun u => seriesTerm z u j) μ := by
  simp_rw [seriesTerm_eq]
  exact (integrable_complex_evenPower μ b j hb hG).const_mul _

theorem integral_norm_seriesTerm_le (μ : Measure U) (b r : ℝ) (z : ℂ)
    (j : ℕ) (hb : 0 < b) (hr : 0 ≤ r) (hz : ‖z‖ ≤ r)
    (hG : Integrable (gaussian b) μ) :
    (∫ u, ‖seriesTerm z u j‖ ∂μ) ≤
      (∫ u, gaussian b u ∂μ) * majorant b r j := by
  calc
    (∫ u, ‖seriesTerm z u j‖ ∂μ) ≤
        ∫ u, majorant b r j * gaussian b u ∂μ :=
      integral_mono (integrable_seriesTerm μ b z j hb hG).norm
        (hG.const_mul _) (fun u => seriesTerm_norm_le z u j b r hb hr hz)
    _ = (∫ u, gaussian b u ∂μ) * majorant b r j := by
      rw [integral_const_mul, mul_comm]

/-- Absolute summability is proved for the actual integrated norms. -/
theorem summable_integral_norm_seriesTerm (μ : Measure U) (b r : ℝ) (z : ℂ)
    (hb : 0 < b) (hr : 0 ≤ r) (hz : ‖z‖ ≤ r)
    (hG : Integrable (gaussian b) μ) :
    Summable (fun j => ∫ u, ‖seriesTerm z u j‖ ∂μ) := by
  apply Summable.of_nonneg_of_le
    (fun j => integral_nonneg (fun _ => norm_nonneg _))
    (fun j => integral_norm_seriesTerm_le μ b r z j hb hr hz hG)
  exact (majorant_hasSum b r).summable.mul_left _

/-- Exact uniform disk budget: no finite-prefix or probability normalization. -/
theorem tsum_integral_norm_seriesTerm_le (μ : Measure U) (b r : ℝ) (z : ℂ)
    (hb : 0 < b) (hr : 0 ≤ r) (hz : ‖z‖ ≤ r)
    (hG : Integrable (gaussian b) μ) :
    (∑' j, ∫ u, ‖seriesTerm z u j‖ ∂μ) ≤
      (∫ u, gaussian b u ∂μ) * Real.exp (r / b) := by
  have h := (summable_integral_norm_seriesTerm μ b r z hb hr hz hG).tsum_le_tsum
    (fun j => integral_norm_seriesTerm_le μ b r z j hb hr hz hG)
    ((majorant_hasSum b r).summable.mul_left (∫ u, gaussian b u ∂μ))
  simpa only [((majorant_hasSum b r).mul_left (∫ u, gaussian b u ∂μ)).tsum_eq] using h

theorem integral_seriesTerm (μ : Measure U) (b : ℝ) (z : ℂ) (j : ℕ)
    (hb : 0 < b) (hG : Integrable (gaussian b) μ) :
    (∫ u, seriesTerm z u j ∂μ) =
      ((-1 : ℂ) ^ j * z ^ j / ((2 * j).factorial : ℂ)) *
        ((∫ u, evenPower j u ∂μ) : ℂ) := by
  simp_rw [seriesTerm_eq]
  rw [integral_const_mul, integral_complex_ofReal]

/-- The Bochner interchange theorem is used only after its absolute-norm
summability premise and every term's actual integrability have been proved. -/
theorem integral_nativeKernel_hasSum (μ : Measure U) (b : ℝ) (z : ℂ)
    (hb : 0 < b) (hG : Integrable (gaussian b) μ) :
    HasSum (fun j => ∫ u, seriesTerm z u j ∂μ)
      (∫ u, nativeKernel z u ∂μ) := by
  exact hasSum_integral_of_summable_integral_norm
    (fun j => integrable_seriesTerm μ b z j hb hG)
    (summable_integral_norm_seriesTerm μ b ‖z‖ z hb (norm_nonneg _) le_rfl hG)

theorem integral_seriesTerm_difference (μp μm : Measure U) (b : ℝ)
    (z : ℂ) (j : ℕ) (hb : 0 < b)
    (hG : Integrable (gaussian b) (μp + μm)) :
    (∫ u, seriesTerm z u j ∂μp) - (∫ u, seriesTerm z u j ∂μm) =
      momentCoefficient μp μm j * z ^ j := by
  rw [integral_seriesTerm μp b z j hb hG.left_of_add_measure,
    integral_seriesTerm μm b z j hb hG.right_of_add_measure]
  simp only [momentCoefficient, signedMoment, Complex.ofReal_sub, integral_complex_ofReal]
  ring

theorem norm_momentTerm_le (μp μm : Measure U) (b : ℝ) (z : ℂ) (j : ℕ)
    (hb : 0 < b) (hG : Integrable (gaussian b) (μp + μm)) :
    ‖momentCoefficient μp μm j * z ^ j‖ ≤
      ∫ u, ‖seriesTerm z u j‖ ∂(μp + μm) := by
  rw [← integral_seriesTerm_difference μp μm b z j hb hG]
  calc
    ‖(∫ u, seriesTerm z u j ∂μp) - (∫ u, seriesTerm z u j ∂μm)‖ ≤
        ‖∫ u, seriesTerm z u j ∂μp‖ + ‖∫ u, seriesTerm z u j ∂μm‖ := norm_sub_le _ _
    _ ≤ (∫ u, ‖seriesTerm z u j‖ ∂μp) +
        (∫ u, ‖seriesTerm z u j‖ ∂μm) :=
      add_le_add (norm_integral_le_integral_norm _) (norm_integral_le_integral_norm _)
    _ = ∫ u, ‖seriesTerm z u j‖ ∂(μp + μm) :=
      (integral_add_measure
        (integrable_seriesTerm μp b z j hb hG.left_of_add_measure).norm
        (integrable_seriesTerm μm b z j hb hG.right_of_add_measure).norm).symm

/-- This is the locally uniform coefficient-norm summability interface used
by the analytic half. It includes radius zero and the constant coefficient. -/
theorem summable_coefficient_norm_radius (μp μm : Measure U) (b r : ℝ)
    (hb : 0 < b) (hr : 0 ≤ r)
    (hG : Integrable (gaussian b) (μp + μm)) :
    Summable (fun j => ‖momentCoefficient μp μm j‖ * r ^ j) := by
  have hz : ‖(r : ℂ)‖ ≤ r := by rw [Complex.norm_of_nonneg hr]
  have hbound (j : ℕ) : ‖momentCoefficient μp μm j‖ * r ^ j ≤
      ∫ u, ‖seriesTerm (r : ℂ) u j‖ ∂(μp + μm) := by
    simpa only [norm_mul, norm_pow, Complex.norm_of_nonneg hr] using
      norm_momentTerm_le μp μm b (r : ℂ) j hb hG
  exact Summable.of_nonneg_of_le (fun _ => by positivity) hbound
    (summable_integral_norm_seriesTerm (μp + μm) b r (r : ℂ) hb hr hz hG)

theorem signedPair_nativeKernel_hasSum (μp μm : Measure U) (b : ℝ) (z : ℂ)
    (hb : 0 < b) (hG : Integrable (gaussian b) (μp + μm)) :
    HasSum (fun j => momentCoefficient μp μm j * z ^ j)
      (signedPair μp μm (nativeKernel z)) := by
  have hp := integral_nativeKernel_hasSum μp b z hb hG.left_of_add_measure
  have hm := integral_nativeKernel_hasSum μm b z hb hG.right_of_add_measure
  unfold signedPair
  convert hp.sub hm using 1
  funext j
  exact (integral_seriesTerm_difference μp μm b z j hb hG).symm

theorem signedPair_nativeKernel_eq (μp μm : Measure U) (b : ℝ) (z : ℂ)
    (hb : 0 < b) (hG : Integrable (gaussian b) (μp + μm)) :
    signedPair μp μm (nativeKernel z) = momentTransform μp μm z :=
  (signedPair_nativeKernel_hasSum μp μm b z hb hG).tsum_eq.symm

end SignedJensenEntirePrep

-- Requested future checks only; these are not compiler axiom reports.
#print axioms SignedJensenEntirePrep.factorial_square_le
#print axioms SignedJensenEntirePrep.seriesTerm_norm_le
#print axioms SignedJensenEntirePrep.summable_integral_norm_seriesTerm
#print axioms SignedJensenEntirePrep.tsum_integral_norm_seriesTerm_le
#print axioms SignedJensenEntirePrep.integral_nativeKernel_hasSum
#print axioms SignedJensenEntirePrep.summable_coefficient_norm_radius
#print axioms SignedJensenEntirePrep.signedPair_nativeKernel_hasSum
#print axioms SignedJensenEntirePrep.signedPair_nativeKernel_eq


/-!
# Entire actual signed-pair transform: uncompiled preparation

This complete proposed proof is static preparation only. No compiler launch,
admission check, successful axiom report or new theorem acceptance is claimed.
`MomentInterchange` supplies actual Gaussian-dominated absolute convergence and
the actual positive-pair integral dictionary, not a conclusion-shaped premise.

Each point is enclosed by an open disk with a summable coefficient majorant.
The pinned locally uniform holomorphic-series theorem supplies complex
differentiability; the pinned Cauchy theorem then supplies analyticity.
No derivative series is interchanged with an integral or sum here.
-/

noncomputable section

open MeasureTheory
open SignedJensenMeasurePrep
open scoped BigOperators

namespace SignedJensenEntirePrep

/-- The full moment transform is complex differentiable at every point.
The fixed Gaussian hypothesis is the actual input, not an entire-transform
assumption. The open disks vary with the point; they cover all of `ℂ`. -/
theorem differentiable_momentTransform (μp μm : Measure U) (b : ℝ)
    (hb : 0 < b) (hG : Integrable (gaussian b) (μp + μm)) :
    Differentiable ℂ (momentTransform μp μm) := by
  intro z
  let r : ℝ := ‖z‖ + 1
  have hr : 0 < r := by dsimp [r]; positivity
  have hmajor : Summable (fun j : ℕ =>
      ‖momentCoefficient μp μm j‖ * r ^ j) :=
    summable_coefficient_norm_radius μp μm b r hb hr.le hG
  have hdiff : DifferentiableOn ℂ (momentTransform μp μm)
      (Metric.ball (0 : ℂ) r) := by
    change DifferentiableOn ℂ (fun w : ℂ =>
      ∑' j : ℕ, momentCoefficient μp μm j * w ^ j)
      (Metric.ball (0 : ℂ) r)
    apply Complex.differentiableOn_tsum_of_summable_norm hmajor
    · intro j
      exact ((differentiable_const (momentCoefficient μp μm j)).mul
        (differentiable_id.pow j)).differentiableOn
    · exact Metric.isOpen_ball
    · intro j w hw
      have hwr : ‖w‖ ≤ r :=
        (by simpa only [Metric.mem_ball, dist_zero_right] using hw : ‖w‖ < r).le
      rw [norm_mul, norm_pow]
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (norm_nonneg w) hwr j) (norm_nonneg _)
  have hz : z ∈ Metric.ball (0 : ℂ) r := by
    change dist z 0 < r
    rw [dist_zero_right]
    dsimp [r]
    linarith
  exact hdiff.differentiableAt (Metric.isOpen_ball.mem_nhds hz)

/-- Entirety is stated as actual complex analyticity at every point, rather
than as real differentiability or an assertion of formal coefficients. -/
theorem analyticAt_momentTransform (μp μm : Measure U) (b : ℝ)
    (hb : 0 < b) (hG : Integrable (gaussian b) (μp + μm)) (z : ℂ) :
    AnalyticAt ℂ (momentTransform μp μm) z :=
  (differentiable_momentTransform μp μm b hb hG).analyticAt z

/-- The actual complete kernel integral is identified pointwise before
transferring differentiability from the coefficient series. An arbitrary
positive pair is not asserted to be a Jordan pair. -/
theorem differentiable_signedPair_nativeKernel (μp μm : Measure U) (b : ℝ)
    (hb : 0 < b) (hG : Integrable (gaussian b) (μp + μm)) :
    Differentiable ℂ (fun z : ℂ => signedPair μp μm (nativeKernel z)) := by
  have hfun : (fun z : ℂ => signedPair μp μm (nativeKernel z)) =
      momentTransform μp μm := by
    funext z
    exact signedPair_nativeKernel_eq μp μm b z hb hG
  rw [hfun]
  exact differentiable_momentTransform μp μm b hb hG

/-- Terminal actual-integral entire theorem. No radius, disk or finite-degree
restriction remains in its conclusion; only the actual Gaussian input does. -/
theorem analyticAt_signedPair_nativeKernel (μp μm : Measure U) (b : ℝ)
    (hb : 0 < b) (hG : Integrable (gaussian b) (μp + μm)) (z : ℂ) :
    AnalyticAt ℂ (fun z : ℂ => signedPair μp μm (nativeKernel z)) z :=
  (differentiable_signedPair_nativeKernel μp μm b hb hG).analyticAt z

end SignedJensenEntirePrep

-- Requested future audits only; no compiler output has been produced.
#print axioms SignedJensenEntirePrep.differentiable_momentTransform
#print axioms SignedJensenEntirePrep.analyticAt_momentTransform
#print axioms SignedJensenEntirePrep.differentiable_signedPair_nativeKernel
#print axioms SignedJensenEntirePrep.analyticAt_signedPair_nativeKernel
