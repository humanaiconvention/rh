import RhExponentialPlancherel001
import RhFinitePrimitiveIntegrability001

noncomputable section
open Set MeasureTheory Filter FourierTransform
open scoped Topology BigOperators ENNReal ComplexInnerProductSpace Convolution
namespace RhTail

def complexExtension (A : ℝ) (w : ℝ → ℝ) (t : ℝ) : ℂ :=
  RhAnchored.zeroExtension A w t

lemma complexExtension_integrable {A : ℝ} {w : ℝ → ℝ}
    (hw : MemLp w 2 (RhAnchored.physicalMeasure A)) :
    Integrable (complexExtension A w) volume :=
  (RhAnchored.zeroExtension_integrable hw).ofReal

lemma complexExtension_memLp {A : ℝ} {w : ℝ → ℝ}
    (hw : MemLp w 2 (RhAnchored.physicalMeasure A)) :
    MemLp (complexExtension A w) 2 volume := by
  have he : MemLp (RhAnchored.zeroExtension A w) 2 volume :=
    (memLp_indicator_iff_restrict measurableSet_Icc.nullMeasurableSet).mpr hw
  exact he.ofReal

def physicalFourierVector (A : ℝ) (w : ℝ → ℝ)
    (hw : MemLp w 2 (RhAnchored.physicalMeasure A)) : WholeSpace :=
  (complexExtension_memLp hw).toLp (complexExtension A w)

lemma exponentialConvolution_complexExtension (A β : ℝ) (w : ℝ → ℝ) (t : ℝ) :
    exponentialConvolution β (complexExtension A w) t =
      ((RhAnchored.exponentialOperator A β w t : ℝ) : ℂ) := by
  unfold exponentialConvolution
  rw [convolution_mul_swap]
  change (∫ u : ℝ, ((Real.exp (-β*|t-u|) : ℝ) : ℂ)*
    ((RhAnchored.zeroExtension A w u : ℝ) : ℂ)) = _
  simp only [← Complex.ofReal_mul]
  calc
    _ = ((∫ u : ℝ, Real.exp (-β*|t-u|)*RhAnchored.zeroExtension A w u : ℝ) : ℂ) :=
      integral_complex_ofReal
    _ = _ := by
      apply congrArg Complex.ofReal
      unfold RhAnchored.exponentialOperator
      have hs : MeasurableSet (RhAnchored.interval A) := measurableSet_Icc
      rw [← integral_indicator hs]
      apply integral_congr_ae
      exact Eventually.of_forall (fun u => by
        by_cases hu : u ∈ RhAnchored.interval A
        · simp [RhAnchored.zeroExtension, hu]
        · simp [RhAnchored.zeroExtension, hu])

lemma complexExtension_norm_integral (A : ℝ) (w : ℝ → ℝ) :
    (∫ t : ℝ, ‖complexExtension A w t‖^2) =
      ∫ t in RhAnchored.interval A, w t^2 := by
  have hs : MeasurableSet (RhAnchored.interval A) := measurableSet_Icc
  rw [← integral_indicator hs]
  apply integral_congr_ae
  exact Eventually.of_forall (fun t => by
    by_cases ht : t ∈ RhAnchored.interval A
    · simp [complexExtension, RhAnchored.zeroExtension, ht, Real.norm_eq_abs, sq_abs]
    · simp [complexExtension, RhAnchored.zeroExtension, ht])

lemma complexExtension_pair_integral (A β : ℝ) (w : ℝ → ℝ) :
    (∫ t : ℝ, (inner ℂ (complexExtension A w t)
      (exponentialConvolution β (complexExtension A w) t)).re) =
    ∫ t in RhAnchored.interval A, RhAnchored.exponentialOperator A β w t*w t := by
  have hs : MeasurableSet (RhAnchored.interval A) := measurableSet_Icc
  rw [← integral_indicator hs]
  apply integral_congr_ae
  exact Eventually.of_forall (fun t => by
    dsimp only
    rw [exponentialConvolution_complexExtension]
    by_cases ht : t ∈ RhAnchored.interval A
    · simp only [complexExtension, RhAnchored.zeroExtension, indicator_of_mem ht,
        RCLike.inner_apply, Complex.conj_ofReal, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, mul_zero, sub_zero]
    · simp [complexExtension, RhAnchored.zeroExtension, ht])

lemma physical_exponential_continuous {A β : ℝ} (hβ : 0 ≤ β)
    {w : ℝ → ℝ} (hw : MemLp w 2 (RhAnchored.physicalMeasure A)) :
    Continuous (RhAnchored.exponentialOperator A β w) := by
  have hc := Complex.continuous_re.comp
    (exponentialConvolution_continuous hβ (complexExtension_integrable hw))
  convert hc using 1
  funext t
  dsimp only [Function.comp_def]
  rw [exponentialConvolution_complexExtension]
  rfl

lemma physical_exponential_pair_integrable {A β : ℝ} (hβ : 0 ≤ β)
    {w : ℝ → ℝ} (hw : MemLp w 2 (RhAnchored.physicalMeasure A)) :
    IntegrableOn (fun t => RhAnchored.exponentialOperator A β w t*w t)
      (RhAnchored.interval A) := by
  have hi : IntegrableOn w (RhAnchored.interval A) := hw.integrable (by norm_num)
  exact hi.continuousOn_mul
    (physical_exponential_continuous hβ hw).continuousOn isCompact_Icc

lemma physical_square_integrable {A : ℝ} {w : ℝ → ℝ}
    (hw : MemLp w 2 (RhAnchored.physicalMeasure A)) :
    IntegrableOn (fun t => w t^2) (RhAnchored.interval A) := by
  change Integrable (fun t => w t^2) (RhAnchored.physicalMeasure A)
  simpa only [Real.norm_eq_abs, sq_abs] using
    (memLp_two_iff_integrable_sq_norm hw.aestronglyMeasurable).mp hw

theorem physical_exponential_plancherel {A β : ℝ} (hβ : 0 < β)
    {w : ℝ → ℝ} (hw : MemLp w 2 (RhAnchored.physicalMeasure A)) :
    (2/β)*(∫ t in RhAnchored.interval A, w t^2) -
      (∫ t in RhAnchored.interval A, RhAnchored.exponentialOperator A β w t*w t) =
    ∫ ξ : ℝ, multiplier (angularSquare ξ) β*
      spectralDensity (physicalFourierVector A w hw) ξ := by
  have hp := exponential_difference_plancherel hβ
    (complexExtension_integrable hw) (complexExtension_memLp hw)
  rw [complexExtension_norm_integral, complexExtension_pair_integral] at hp
  exact hp

end RhTail
#print axioms RhTail.physical_exponential_plancherel
