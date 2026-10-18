import RhPrimeHingeIntegrability001
import RhPrimitiveFormDomain001

/-!
All-radius real physical-to-primitive dictionary. The archimedean series is
complete and every prescribed finite prime-power weight is retained. This
identity is independent of any positivity claim or spectral-domain equality.
-/
noncomputable section
open Set MeasureTheory Filter FourierTransform
open scoped Topology BigOperators ENNReal
namespace RhCompletePrimitiveDictionary
open RhAnchored RhAllPrime RhPrimeHingeIntegrability

/-- The scalar and BOTH archimedean ranks, with their native signs. -/
def rankScalar (R C : ℝ) (w : ℝ → ℝ) : ℝ :=
  -C * (∫ t in interval R, (w t)^2) +
    2 * (∫ t in interval R, Real.cosh (t / 2) * w t)^2 -
    2 * (∫ t in interval R, Real.sinh (t / 2) * w t)^2

lemma zero_weight_fullKernel (C L L' t u : ℝ) :
    fullKernel C 0 L t u = fullKernel C 0 L' t u := by
  simp only [fullKernel, finiteKernel, anchoredKernel, finitePotential,
    zero_mul, add_zero]

lemma arch_zero_head_identity {R : ℝ} (hR : 0 < R)
    {v : ℝ → ℝ} (hv : MemLp v 2 (physicalMeasure R)) (C : ℝ) :
    finiteQuadratic R C 0 (R + 1) 0 v = rankScalar R C (primitive R v) := by
  let w := primitive R v
  have hw := primitive_memLp hv
  have hw1 : IntegrableOn w (interval R) := hw.integrable (by norm_num)
  have hi0 : IntegrableOn (fun t => -C * (w t)^2) (interval R) :=
    (RhTail.physical_square_integrable hw).const_mul _
  have hiC : IntegrableOn (fun t =>
      2 * Real.cosh (t / 2) * (∫ u in interval R, Real.cosh (u / 2) * w u) * w t)
      (interval R) := hw1.continuousOn_mul (by fun_prop) isCompact_Icc
  have hiS : IntegrableOn (fun t =>
      2 * Real.sinh (t / 2) * (∫ u in interval R, Real.sinh (u / 2) * w u) * w t)
      (interval R) := hw1.continuousOn_mul (by fun_prop) isCompact_Icc
  unfold finiteQuadratic kernelQuadratic
  rw [finite_J_Schur_identity hR (by linarith : R < R + 1) hv C 0 0]
  have hfun : (fun t => nativeOperator R C 0 (R + 1) 0 w t * w t) =
      (fun t => -C * (w t)^2 +
        2 * Real.cosh (t / 2) * (∫ u in interval R, Real.cosh (u / 2) * w u) * w t -
        2 * Real.sinh (t / 2) * (∫ u in interval R, Real.sinh (u / 2) * w u) * w t) := by
    funext t
    simp only [nativeOperator, nativeDiagonal, Finset.sum_range_zero]
    ring
  change (∫ t in interval R, nativeOperator R C 0 (R + 1) 0 w t * w t) = _
  rw [hfun]
  have hsub := integral_sub (hi0.add hiC) hiS
  have hadd := integral_add hi0 hiC
  simp only [Pi.sub_apply, Pi.add_apply] at hsub hadd
  rw [hsub, hadd]
  have hc : (∫ t in interval R,
      2 * Real.cosh (t / 2) * (∫ u in interval R, Real.cosh (u / 2) * w u) * w t) =
      2 * (∫ t in interval R, Real.cosh (t / 2) * w t)^2 := by
    calc
      _ = (2 * (∫ u in interval R, Real.cosh (u / 2) * w u)) *
          (∫ t in interval R, Real.cosh (t / 2) * w t) := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        exact Eventually.of_forall (fun t => by ring)
      _ = _ := by ring
  have hs : (∫ t in interval R,
      2 * Real.sinh (t / 2) * (∫ u in interval R, Real.sinh (u / 2) * w u) * w t) =
      2 * (∫ t in interval R, Real.sinh (t / 2) * w t)^2 := by
    calc
      _ = (2 * (∫ u in interval R, Real.sinh (u / 2) * w u)) *
          (∫ t in interval R, Real.sinh (t / 2) * w t) := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        exact Eventually.of_forall (fun t => by ring)
      _ = _ := by ring
  rw [hc, hs, integral_const_mul]
  rfl

/-- The positive complete Fourier energy is finite on the actual primitive;
its `toReal` below is not used on an infinite-energy vector. -/
theorem arch_only_identity {R : ℝ} (hR : 0 < R)
    {v : ℝ → ℝ} (hv : MemLp v 2 (physicalMeasure R)) (C : ℝ) :
    fullQuadratic R C 0 (R + 1) v =
      (RhTail.fullFrequencyEnergy (1 / 2)
        (RhTail.physicalFourierVector R (primitive R v) (primitive_memLp hv))).toReal +
      rankScalar R C (primitive R v) := by
  have ht := RhTail.physical_fourier_tail_limit hR (by linarith : R < R + 1) hv C 0 0
  have hb : beta 0 = (1 / 2 : ℝ) := by norm_num [beta, archIndex]
  rw [hb] at ht
  have he : (RhTail.fullFrequencyEnergy (1 / 2)
      (RhTail.physicalFourierVector R (primitive R v) (primitive_memLp hv))).toReal =
      fullQuadratic R C 0 (R + 1) v - finiteQuadratic R C 0 (R + 1) 0 v := by
    rw [ht.1, ENNReal.toReal_ofReal ht.2]
  rw [arch_zero_head_identity hR hv C] at he
  linarith

lemma arithmetic_as_hinge_sum (N : ℕ) :
    arithmeticKernel N = fun t u => ∑ n ∈ Finset.Icc 2 N,
      RhSupportPrimeHinge.primeHinge (weight n) (Real.log (n : ℝ)) t u := by
  funext t u
  unfold arithmeticKernel
  apply Finset.sum_congr rfl
  intro n hn
  unfold hingeKernel RhSupportPrimeHinge.primeHinge anchoredKernel
  ring

/-- Exact finite prime-power dictionary, including every old and newly active hinge. -/
theorem arithmetic_primitive_identity {R : ℝ} (hR : 0 < R)
    {v : ℝ → ℝ} (hv : MemLp v 2 (physicalMeasure R)) (N : ℕ) :
    kernelQuadratic R (arithmeticKernel N) v =
      -(∑ n ∈ Finset.Icc 2 N, weight n * (∫ t in interval R,
        primeShift R (Real.log (n : ℝ)) (primitive R v) t * primitive R v t)) := by
  rw [arithmetic_as_hinge_sum]
  apply finite_hinge_sum_identity (Finset.Icc 2 N) weight (fun n => Real.log (n : ℝ))
    _ hR hv
  intro n hn
  apply Real.log_pos
  have hn2 : 2 ≤ n := (Finset.mem_Icc.mp hn).1
  exact_mod_cast (lt_of_lt_of_le (by decide : (1 : ℕ) < 2) hn2)

/-- All radii and arbitrary exact finite cutoff. No positivity is assumed. -/
theorem complete_cutoff_native_identity {R : ℝ} (hR : 0 < R)
    {v : ℝ → ℝ} (hv : MemLp v 2 (physicalMeasure R)) (N : ℕ) :
    kernelQuadratic R (completeKernel N) v =
      (RhTail.fullFrequencyEnergy (1 / 2)
        (RhTail.physicalFourierVector R (primitive R v) (primitive_memLp hv))).toReal +
      rankScalar R archConstant (primitive R v) -
      (∑ n ∈ Finset.Icc 2 N, weight n * (∫ t in interval R,
        primeShift R (Real.log (n : ℝ)) (primitive R v) t * primitive R v t)) := by
  have hk : fullKernel archConstant 0 0 = fullKernel archConstant 0 (R + 1) := by
    funext t u
    exact zero_weight_fullKernel _ _ _ _ _
  have ha : kernelQuadratic R (fullKernel archConstant 0 0) v =
      (RhTail.fullFrequencyEnergy (1 / 2)
        (RhTail.physicalFourierVector R (primitive R v) (primitive_memLp hv))).toReal +
      rankScalar R archConstant (primitive R v) := by
    rw [hk]
    exact arch_only_identity hR hv archConstant
  unfold completeKernel
  rw [RhDilationNative.kernelQuadratic_add
    (RhEndpointComplex.fullKernel_joint_continuous _ _ _)
    (arithmetic_joint_continuous N) hv, ha, arithmetic_primitive_identity hR hv N]
  ring

/-- The actual radius cutoff is exactly floor(exp(2R)); no smoothing is used. -/
theorem all_radius_native_identity {R : ℝ} (hR : 0 < R)
    {v : ℝ → ℝ} (hv : MemLp v 2 (physicalMeasure R)) :
    kernelQuadratic R (radiusKernel R) v =
      (RhTail.fullFrequencyEnergy (1 / 2)
        (RhTail.physicalFourierVector R (primitive R v) (primitive_memLp hv))).toReal +
      rankScalar R archConstant (primitive R v) -
      (∑ n ∈ Finset.Icc 2 (radiusCutoff R), weight n * (∫ t in interval R,
        primeShift R (Real.log (n : ℝ)) (primitive R v) t * primitive R v t)) :=
  complete_cutoff_native_identity hR hv (radiusCutoff R)

end RhCompletePrimitiveDictionary
#print axioms RhCompletePrimitiveDictionary.arch_only_identity
#print axioms RhCompletePrimitiveDictionary.arithmetic_primitive_identity
#print axioms RhCompletePrimitiveDictionary.complete_cutoff_native_identity
#print axioms RhCompletePrimitiveDictionary.all_radius_native_identity
