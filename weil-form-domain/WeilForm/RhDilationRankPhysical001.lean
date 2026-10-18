import RhDilationRankPerturbation001
import RhDilationPhysical001

noncomputable section
open Set MeasureTheory Filter
open scoped Topology Interval BigOperators

namespace RhDilationRank
open RhAnchored RhDilation

/-- Actual interval Jacobian and native square-root normalization. -/
theorem moment_dilate {A r : ℝ} (hA : 0 < A) (hr : 0 < r)
    (f w : ℝ → ℝ) :
    moment (r * A) (profile f 1) (dilate r w) = moment A (profile f r) w := by
  have hcoef : r * (Real.sqrt r)⁻¹ = Real.sqrt r := by
    rw [←div_eq_mul_inv]
    apply (div_eq_iff (Real.sqrt_pos.mpr hr).ne').2
    nlinarith [Real.sq_sqrt hr.le]
  have hpoint (x : ℝ) :
      r * (f ((r * x) / 2) * dilate r w (r * x)) = profile f r x * w x := by
    unfold dilate profile
    have hdiv : r * x / r = x := by field_simp
    rw [hdiv]
    calc
      r * (f (r * x / 2) * ((Real.sqrt r)⁻¹ * w x)) =
          (r * (Real.sqrt r)⁻¹) * (f (r * x / 2) * w x) := by ring
      _ = _ := by rw [hcoef]; ring
  have hsub := intervalIntegral.smul_integral_comp_mul_left
    (a := -A) (b := A) (fun t : ℝ => f (t / 2) * dilate r w t) r
  have hR : -(r * A) ≤ r * A := by linarith [mul_pos hr hA]
  have hI : -A ≤ A := by linarith
  unfold moment
  change (∫ t in interval (r * A), (Real.sqrt 1 * f (1 * t / 2)) * dilate r w t) = _
  simp only [Real.sqrt_one,one_mul]
  calc
    _ = ∫ t in -(r * A)..(r * A), f (t / 2) * dilate r w t := by
      rw [intervalIntegral.integral_of_le hR,interval,integral_Icc_eq_integral_Ioc]
    _ = r * (∫ x in -A..A, f ((r * x) / 2) * dilate r w (r * x)) := by
      simpa only [smul_eq_mul,show r * (-A) = -(r * A) by ring] using hsub.symm
    _ = ∫ x in -A..A, profile f r x * w x := by
      rw [←intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro x hx
      exact hpoint x
    _ = _ := by
      rw [intervalIntegral.integral_of_le hI,interval,integral_Icc_eq_integral_Ioc]

/-- Both actual moments, including their native factors, transform together. -/
theorem physical_rank_dilate {A r : ℝ} (hA : 0 < A) (hr : 0 < r) (w : ℝ → ℝ) :
    rankForm (r * A) 1 (dilate r w) = rankForm A r w := by
  unfold rankForm coshProfile sinhProfile
  rw [moment_dilate hA hr,moment_dilate hA hr]

/-- Actual physical rank perturbation, without a profile-continuity hypothesis. -/
theorem exists_physical_rank_perturbation_bound {A : ℝ} (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, 1 ≤ r → r ≤ 2 →
      ∀ w : ℝ → ℝ, MemLp w 2 (physicalMeasure A) →
        |rankForm (r * A) 1 (dilate r w) - rankForm A 1 w| ≤
          C * (r - 1) * (∫ t in interval A, (w t) ^ 2) := by
  obtain ⟨C,hC,hbound⟩ := exists_rank_perturbation_bound hA
  refine ⟨C,hC,?_⟩
  intro r hr1 hr2 w hw
  rw [physical_rank_dilate hA (by linarith : 0 < r)]
  exact hbound r hr1 hr2 w hw

end RhDilationRank
#print axioms RhDilationRank.moment_dilate
#print axioms RhDilationRank.physical_rank_dilate
#print axioms RhDilationRank.exists_physical_rank_perturbation_bound

