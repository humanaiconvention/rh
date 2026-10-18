import RhDilationRankProfiles001

noncomputable section
open Set MeasureTheory Filter
open scoped Topology BigOperators

namespace RhDilationRank
open RhAnchored

def moment (A : ℝ) (f w : ℝ → ℝ) : ℝ := ∫ t in interval A, f t * w t

def rankForm (A r : ℝ) (w : ℝ → ℝ) : ℝ :=
  2 * (moment A (coshProfile r) w) ^ 2 - 2 * (moment A (sinhProfile r) w) ^ 2

lemma moment_abs_le {A B : ℝ} {f w : ℝ → ℝ}
    (hf : Continuous f) (hw : MemLp w 2 (physicalMeasure A))
    (hB : ∀ t ∈ interval A, |f t| ≤ B) :
    |moment A f w| ≤ B * (∫ t in interval A, |w t|) := by
  have hfw := (continuous_memLp hf).integrable_mul hw
  have hiw := (hw.integrable (by norm_num)).norm
  calc
    _ ≤ ∫ t in interval A, |f t * w t| := by
      simpa only [moment,Real.norm_eq_abs] using
        norm_integral_le_integral_norm (fun t : ℝ => f t * w t)
    _ ≤ ∫ t in interval A, B * |w t| := by
      apply integral_mono_ae hfw.norm (hiw.const_mul B)
      exact ae_restrict_of_forall_mem measurableSet_Icc (fun t ht => by
        simpa only [Pi.mul_apply,Real.norm_eq_abs,abs_mul] using
          mul_le_mul_of_nonneg_right (hB t ht) (abs_nonneg (w t)))
    _ = _ := integral_const_mul _ _

lemma moment_sub (A : ℝ) {f g w : ℝ → ℝ}
    (hf : Continuous f) (hg : Continuous g) (hw : MemLp w 2 (physicalMeasure A)) :
    moment A (fun t => f t - g t) w = moment A f w - moment A g w := by
  unfold moment
  simp_rw [sub_mul]
  exact integral_sub ((continuous_memLp hf).integrable_mul hw)
    ((continuous_memLp hg).integrable_mul hw)

lemma scalar_square_difference {c d B D W : ℝ} (hB : 0 ≤ B) (hD : 0 ≤ D) (hW : 0 ≤ W)
    (hc : |c| ≤ B * W) (hd : |d| ≤ B * W) (hcd : |c - d| ≤ D * W) :
    |c ^ 2 - d ^ 2| ≤ 2 * B * D * W ^ 2 := by
  have hs : |c + d| ≤ 2 * B * W := (abs_add_le c d).trans (by linarith)
  have he : c ^ 2 - d ^ 2 = (c - d) * (c + d) := by ring
  rw [he,abs_mul]
  have hh := mul_le_mul hcd hs (abs_nonneg (c + d)) (by positivity : 0 ≤ D * W)
  nlinarith [hh]

/-- Uniform whole-rank perturbation; the coefficient is finite and proved to exist. -/
theorem exists_rank_perturbation_bound {A : ℝ} (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, 1 ≤ r → r ≤ 2 →
      ∀ w : ℝ → ℝ, MemLp w 2 (physicalMeasure A) →
        |rankForm A r w - rankForm A 1 w| ≤
          C * (r - 1) * (∫ t in interval A, (w t) ^ 2) := by
  obtain ⟨B,hB,K,hK,hbounds⟩ := exists_native_profile_bounds hA
  refine ⟨16 * A * B * K, by positivity, ?_⟩
  intro r hr1 hr2 w hw
  let W : ℝ := ∫ t in interval A, |w t|
  have hW : 0 ≤ W := integral_nonneg (fun t => abs_nonneg _)
  have hdelta : 0 ≤ r - 1 := by linarith
  have hc : |moment A (coshProfile r) w| ≤ B * W :=
    moment_abs_le (profile_continuous Real.continuous_cosh r) hw
      (fun t ht => (hbounds r hr1 hr2 t ht).1)
  have hs : |moment A (sinhProfile r) w| ≤ B * W :=
    moment_abs_le (profile_continuous Real.continuous_sinh r) hw
      (fun t ht => (hbounds r hr1 hr2 t ht).2.1)
  have hc1 : |moment A (coshProfile 1) w| ≤ B * W :=
    moment_abs_le (profile_continuous Real.continuous_cosh 1) hw
      (fun t ht => (hbounds 1 le_rfl (by norm_num) t ht).1)
  have hs1 : |moment A (sinhProfile 1) w| ≤ B * W :=
    moment_abs_le (profile_continuous Real.continuous_sinh 1) hw
      (fun t ht => (hbounds 1 le_rfl (by norm_num) t ht).2.1)
  have hdc : |moment A (coshProfile r) w - moment A (coshProfile 1) w| ≤
      (K * (r - 1)) * W := by
    change |moment A (profile Real.cosh r) w - moment A (profile Real.cosh 1) w| ≤ (K * (r - 1)) * W
    rw [←moment_sub A (profile_continuous Real.continuous_cosh r)
      (profile_continuous Real.continuous_cosh 1) hw]
    exact moment_abs_le ((profile_continuous Real.continuous_cosh r).sub
      (profile_continuous Real.continuous_cosh 1)) hw
      (fun t ht => (hbounds r hr1 hr2 t ht).2.2.1)
  have hds : |moment A (sinhProfile r) w - moment A (sinhProfile 1) w| ≤
      (K * (r - 1)) * W := by
    change |moment A (profile Real.sinh r) w - moment A (profile Real.sinh 1) w| ≤ (K * (r - 1)) * W
    rw [←moment_sub A (profile_continuous Real.continuous_sinh r)
      (profile_continuous Real.continuous_sinh 1) hw]
    exact moment_abs_le ((profile_continuous Real.continuous_sinh r).sub
      (profile_continuous Real.continuous_sinh 1)) hw
      (fun t ht => (hbounds r hr1 hr2 t ht).2.2.2)
  have hcSq := scalar_square_difference hB.le (mul_nonneg hK.le hdelta) hW hc hc1 hdc
  have hsSq := scalar_square_difference hB.le (mul_nonneg hK.le hdelta) hW hs hs1 hds
  have hpair : |rankForm A r w - rankForm A 1 w| ≤ 8 * B * K * (r - 1) * W ^ 2 := by
    unfold rankForm
    have he : 2 * (moment A (coshProfile r) w) ^ 2 - 2 * (moment A (sinhProfile r) w) ^ 2 -
        (2 * (moment A (coshProfile 1) w) ^ 2 - 2 * (moment A (sinhProfile 1) w) ^ 2) =
        2 * ((moment A (coshProfile r) w) ^ 2 - (moment A (coshProfile 1) w) ^ 2) -
          2 * ((moment A (sinhProfile r) w) ^ 2 - (moment A (sinhProfile 1) w) ^ 2) := by ring
    rw [he]
    calc
      _ ≤ |2 * ((moment A (coshProfile r) w) ^ 2 - (moment A (coshProfile 1) w) ^ 2)| +
          |2 * ((moment A (sinhProfile r) w) ^ 2 - (moment A (sinhProfile 1) w) ^ 2)| :=
        abs_sub _ _
      _ ≤ 8 * B * K * (r - 1) * W ^ 2 := by
        norm_num only [abs_mul]
        nlinarith
  have hCS := l1_sq_le hA hw
  have hmult := mul_le_mul_of_nonneg_left hCS
    (by positivity : 0 ≤ 8 * B * K * (r - 1))
  change 8 * B * K * (r - 1) * W ^ 2 ≤ _ at hmult
  calc
    _ ≤ 8 * B * K * (r - 1) * W ^ 2 := hpair
    _ ≤ 8 * B * K * (r - 1) * (2 * A * (∫ t in interval A, (w t) ^ 2)) := hmult
    _ = _ := by ring

end RhDilationRank
#print axioms RhDilationRank.moment_abs_le
#print axioms RhDilationRank.exists_rank_perturbation_bound


