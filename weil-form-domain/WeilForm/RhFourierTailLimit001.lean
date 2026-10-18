import RhFourierTrapezoid001

noncomputable section
open Set MeasureTheory Filter
open scoped Topology Interval BigOperators
namespace RhTail

lemma multiplier_series_summable {x b : ℝ} (hx : 0 ≤ x) (hb : 1 ≤ b) :
    Summable (fun k : ℕ => multiplier x (b+2*k)) := by
  have hbase : Summable (fun k : ℕ => (1 : ℝ)/(k : ℝ)^2) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < (2 : ℕ))
  have hshift : Summable (fun k : ℕ => (1 : ℝ)/((k : ℝ)+1)^2) := by
    simpa only [Nat.cast_add, Nat.cast_one] using (summable_nat_add_iff 1).mpr hbase
  have hmajor : Summable (fun k : ℕ => 2*x/((k : ℝ)+1)^2) := by
    simpa only [← mul_div_assoc, mul_one] using hshift.mul_left (2*x)
  apply Summable.of_nonneg_of_le (fun k => multiplier_nonneg hx (by positivity)) ?_ hmajor
  intro k
  have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
  have hr : 1 ≤ b+2*(k : ℝ) := by linarith
  have hkr : (k : ℝ)+1 ≤ b+2*k := by linarith
  have hsq : ((k : ℝ)+1)^2 ≤ (b+2*k)^2 := by nlinarith
  have hp : 0 ≤ (b+2*(k : ℝ)-1)*(b+2*k)^2 := by positivity
  have hden : ((k : ℝ)+1)^2 ≤ (b+2*k)*((b+2*k)^2+x) := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ b+2*(k : ℝ)) hx]
  unfold multiplier
  exact div_le_div_of_nonneg_left (by positivity) (by positivity) hden

lemma logarithmic_endpoint_tendsto_zero {x b : ℝ} :
    Tendsto (fun K : ℕ => Real.log (1+x/(b+2*K)^2)) atTop (𝓝 0) := by
  have hn : Tendsto (fun K : ℕ => (K : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have ht : Tendsto (fun K : ℕ => b+2*(K : ℝ)) atTop atTop :=
    tendsto_atTop_add_const_left atTop b (hn.const_mul_atTop (by norm_num : 0 < (2 : ℝ)))
  have hi : Tendsto (fun K : ℕ => (b+2*(K : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp ht
  have hv : Tendsto (fun K : ℕ => 1+x*((b+2*(K : ℝ))⁻¹)^2) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds.add (tendsto_const_nhds.mul (hi.pow 2)))
  have hlog := (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp hv
  simpa only [Function.comp_def, div_eq_mul_inv, inv_pow, Real.log_one] using hlog

theorem infinite_tail_trapezoid {x b : ℝ} (hx : 0 ≤ x) (hb : 1 ≤ b) :
    (1/2)*Real.log (1+x/b^2)+multiplier x b/2 ≤
      ∑' k : ℕ, multiplier x (b+2*k) := by
  have hs := multiplier_series_summable hx hb
  have hlog := logarithmic_endpoint_tendsto_zero (x := x) (b := b)
  have hf : Tendsto (fun K : ℕ => multiplier x (b+2*K)) atTop (𝓝 0) :=
    hs.tendsto_atTop_zero
  have hleft : Tendsto (fun K : ℕ =>
      (1/2)*(Real.log (1+x/b^2)-Real.log (1+x/(b+2*K)^2))+
        (multiplier x b-multiplier x (b+2*K))/2)
      atTop (𝓝 ((1/2)*Real.log (1+x/b^2)+multiplier x b/2)) := by
    have hcL : Tendsto (fun _ : ℕ => Real.log (1+x/b^2)) atTop
        (𝓝 (Real.log (1+x/b^2))) := tendsto_const_nhds
    have hcF : Tendsto (fun _ : ℕ => multiplier x b) atTop
        (𝓝 (multiplier x b)) := tendsto_const_nhds
    simpa only [sub_zero] using ((hcL.sub hlog).const_mul (1/2)).add
      ((hcF.sub hf).div_const 2)
  exact le_of_tendsto_of_tendsto hleft hs.hasSum.tendsto_sum_nat
    (Eventually.of_forall (finite_tail_trapezoid hx (by linarith : 0 < b)))

theorem multiplier_tail_lower_bound {x b : ℝ} (hx : 0 ≤ x) (hb : 1 ≤ b) :
    (1/2+1/b)*x/(b^2+x) ≤ ∑' k : ℕ, multiplier x (b+2*k) := by
  have h := infinite_tail_trapezoid hx hb
  have he : multiplier x b/2=x/(b*(b^2+x)) := by unfold multiplier; ring
  rw [he] at h
  exact (log_comparison hx (by linarith)).trans h

theorem exact_endpoint_multiplier_lower_bound (ξ : ℝ) :
    tailDelta*ξ^2/(tailBeta^2+ξ^2) ≤
      ∑' k : ℕ, multiplier (ξ^2) (tailBeta+2*k) := by
  rw [tail_constants.2.1]
  exact multiplier_tail_lower_bound (sq_nonneg ξ) (by norm_num [tailBeta])

end RhTail
#print axioms RhTail.multiplier_series_summable
#print axioms RhTail.infinite_tail_trapezoid
#print axioms RhTail.exact_endpoint_multiplier_lower_bound
