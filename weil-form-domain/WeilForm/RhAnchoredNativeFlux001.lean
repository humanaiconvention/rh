import RhAnchoredSignedConvolution001
import RhAnchoredCumulativeLedger001

noncomputable section
open MeasureTheory Set Filter
open scoped Topology Interval BigOperators
namespace RhAnchored

def rankFlux (A : ℝ) (w : ℝ → ℝ) (t : ℝ) : ℝ :=
  (-4*(∫ u in interval A, Real.cosh (u/2)*w u))*Real.sinh (t/2)
  +(4*(∫ u in interval A, Real.sinh (u/2)*w u))*(Real.cosh (t/2)-1)

def nativeFlux (A C α L : ℝ) (J : ℕ) (w : ℝ → ℝ) (t : ℝ) : ℝ :=
  rankFlux A w t+C*(leftPrimitive A w t-leftPrimitive A w 0)
  -(∑ k ∈ Finset.range J, (beta k)⁻¹*
    (signedExponentialOperator A (beta k) w t-signedExponentialOperator A (beta k) w 0))
  +α*hingeConvolution A L w t

lemma archIndex_inv_eq_two_beta_inv (k : ℕ) : (archIndex k)⁻¹=2*(beta k)⁻¹ := by
  have ha : archIndex k ≠ 0 := by unfold archIndex; positivity
  unfold beta
  field_simp

lemma rankFlux_hasDerivAt (A : ℝ) (w : ℝ → ℝ) (t : ℝ) :
    HasDerivAt (rankFlux A w)
      (-2*Real.cosh (t/2)*(∫ u in interval A, Real.cosh (u/2)*w u)
       +2*Real.sinh (t/2)*(∫ u in interval A, Real.sinh (u/2)*w u)) t := by
  have hs := (((hasDerivAt_id t).div_const 2).sinh).const_mul
    (-4*(∫ u in interval A, Real.cosh (u/2)*w u))
  have hc := ((((hasDerivAt_id t).div_const 2).cosh).sub_const 1).const_mul
    (4*(∫ u in interval A, Real.sinh (u/2)*w u))
  have h := hs.add hc
  unfold rankFlux
  convert h using 1
  · rfl
  · simp only [id_eq]
    ring

lemma nativeFlux_zero {A L : ℝ} (hA : 0 < A) (hAL : A < L) {v : ℝ → ℝ}
    (hv : MemLp v 2 (physicalMeasure A)) (C α : ℝ) (J : ℕ) :
    nativeFlux A C α L J (primitive A v) 0=0 := by
  have hhinge := hingeConvolution_eq_shiftFlux hA hAL hv 0
  rw [shiftFlux_zero] at hhinge
  simp [nativeFlux, rankFlux, hhinge]

theorem nativeFlux_ac {A L : ℝ} (hA : 0 < A) (hAL : A < L) {v : ℝ → ℝ}
    (hv : MemLp v 2 (physicalMeasure A)) (C α : ℝ) (J : ℕ) :
    AbsolutelyContinuousOnInterval (nativeFlux A C α L J (primitive A v)) (-A) A := by
  have hrank : AbsolutelyContinuousOnInterval (rankFlux A (primitive A v)) (-A) A := by
    unfold rankFlux
    apply ContDiffOn.absolutelyContinuousOnInterval
    fun_prop
  have hcum : AbsolutelyContinuousOnInterval (leftPrimitive A (primitive A v)) (-A) A :=
    (cumulative_primitive_lipschitz hv).lipschitzOnWith.absolutelyContinuousOnInterval
  have hconst : AbsolutelyContinuousOnInterval
      (fun _ : ℝ => leftPrimitive A (primitive A v) 0) (-A) A := by
    apply ContDiffOn.absolutelyContinuousOnInterval
    fun_prop
  have hsum : AbsolutelyContinuousOnInterval
      (fun t => ∑ k ∈ Finset.range J, (beta k)⁻¹*
        (signedExponentialOperator A (beta k) (primitive A v) t-
         signedExponentialOperator A (beta k) (primitive A v) 0)) (-A) A := by
    apply finite_sum_ac
    intro k _
    have hc : AbsolutelyContinuousOnInterval
        (fun _ : ℝ => signedExponentialOperator A (beta k) (primitive A v) 0) (-A) A := by
      apply ContDiffOn.absolutelyContinuousOnInterval
      fun_prop
    exact ((signedExponentialOperator_ac hA hv (beta k)).fun_sub hc).const_mul _
  unfold nativeFlux
  exact ((hrank.fun_add ((hcum.fun_sub hconst).const_mul C)).fun_sub hsum).fun_add
    ((hingeConvolution_ac hA hAL hv).const_mul α)

theorem nativeFlux_hasDerivAt_regular {A L t : ℝ} (hA : 0 < A) (hAL : A < L)
    {v : ℝ → ℝ} (hv : MemLp v 2 (physicalMeasure A)) (C α : ℝ) (J : ℕ)
    (ht : t ∈ Ioo (-A) A) (ht0 : t ≠ 0) (ht1 : t ≠ A-L) (ht2 : t ≠ L-A) :
    HasDerivAt (nativeFlux A C α L J (primitive A v))
      (-nativeOperator A C α L J (primitive A v) t) t := by
  have htI : t ∈ interval A := ⟨ht.1.le, ht.2.le⟩
  have hcum := cumulative_primitive_hasDerivAt hA hv ht0 (ne_of_gt ht.1) (ne_of_lt ht.2)
  rw [zeroExtension_eq htI] at hcum
  have hscalar := (hcum.sub (hasDerivAt_const t (leftPrimitive A (primitive A v) 0))).const_mul C
  have hsum := HasDerivAt.fun_sum (u := Finset.range J) (fun k _ =>
    ((signedExponentialOperator_hasDerivAt hA hv (beta k) ht ht0).sub
      (hasDerivAt_const t (signedExponentialOperator A (beta k) (primitive A v) 0))).const_mul ((beta k)⁻¹))
  have hshift : HasDerivAt (shiftFlux A L (primitive A v))
      (primeShift A L (primitive A v) t) t := by
    apply shiftFlux_hasDerivAt_regular hA hv
    · intro he; linarith [ht.2]
    · intro he; apply ht2; linarith
    · intro he; linarith [ht.2]
    · intro he; linarith [ht.1]
    · intro he; linarith [ht.1]
    · intro he; apply ht1; linarith
  have hfun : hingeConvolution A L (primitive A v)=shiftFlux A L (primitive A v) := by
    funext x
    exact hingeConvolution_eq_shiftFlux hA hAL hv x
  have hhinge : HasDerivAt (hingeConvolution A L (primitive A v))
      (primeShift A L (primitive A v) t) t := by rw [hfun]; exact hshift
  have hd := (((rankFlux_hasDerivAt A (primitive A v) t).add hscalar).sub hsum).add
    (hhinge.const_mul α)
  have hterms (k : ℕ) :
      (beta k)⁻¹*(2*primitive A v t-beta k*exponentialOperator A (beta k) (primitive A v) t)=
      (archIndex k)⁻¹*primitive A v t-exponentialOperator A (beta k) (primitive A v) t := by
    rw [archIndex_inv_eq_two_beta_inv]
    field_simp [ne_of_gt (beta_pos k)]
    <;> ring
  unfold nativeFlux
  convert hd using 1
  simp only [sub_zero, hterms, Finset.sum_sub_distrib, ← Finset.sum_mul]
  unfold nativeOperator nativeDiagonal
  ring

theorem nativeFlux_ae_deriv {A L : ℝ} (hA : 0 < A) (hAL : A < L) {v : ℝ → ℝ}
    (hv : MemLp v 2 (physicalMeasure A)) (C α : ℝ) (J : ℕ) :
    ∀ᵐ t ∂physicalMeasure A,
      deriv (nativeFlux A C α L J (primitive A v)) t=
        -nativeOperator A C α L J (primitive A v) t := by
  unfold physicalMeasure
  rw [ae_restrict_iff' (show MeasurableSet (interval A) from measurableSet_Icc)]
  filter_upwards [ae_ne_const (-A), ae_ne_const A, ae_ne_const 0,
    ae_ne_const (A-L), ae_ne_const (L-A)] with t htL htR ht0 ht1 ht2 htI
  exact (nativeFlux_hasDerivAt_regular hA hAL hv C α J
    ⟨lt_of_le_of_ne htI.1 (Ne.symm htL), lt_of_le_of_ne htI.2 htR⟩ ht0 ht1 ht2).deriv

theorem nativeFlux_pairing {A L : ℝ} (hA : 0 < A) (hAL : A < L) {v : ℝ → ℝ}
    (hv : MemLp v 2 (physicalMeasure A)) (C α : ℝ) (J : ℕ) :
    (∫ t in interval A, nativeFlux A C α L J (primitive A v) t*v t) =
    ∫ t in interval A, nativeOperator A C α L J (primitive A v) t*primitive A v t := by
  have hweak := primitive_parts_setIntegral_anchored hA hv (nativeFlux_ac hA hAL hv C α J)
    (nativeFlux_zero hA hAL hv C α J)
  calc
    _ = ∫ t in interval A, v t*nativeFlux A C α L J (primitive A v) t := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun t => mul_comm _ _)
    _ = -(∫ t in interval A, primitive A v t*deriv (nativeFlux A C α L J (primitive A v)) t) := hweak
    _ = _ := by
      rw [← integral_neg]
      apply integral_congr_ae
      filter_upwards [nativeFlux_ae_deriv hA hAL hv C α J] with t ht
      simp only [ht]
      ring

end RhAnchored
#print axioms RhAnchored.nativeFlux_ac
#print axioms RhAnchored.nativeFlux_ae_deriv
#print axioms RhAnchored.nativeFlux_pairing
