import RhVariationalInfimum001
import RhSmoothDerivativeDictionary001
import RhActualCoreBump001
import RhFlatSmoothCore001
import RhNativeBoundedPartControl001

/-! Actual physical-unit Rayleigh set on the primitive complete domain.
Nonemptiness and boundedness are proved, not assigned by totalized infima.
No positive Rayleigh lower bound is asserted. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology ContDiff
namespace RhNativeRayleighDomain
open RhAnchored RhWeightedMeasureEmbedding RhWeightedPrimitiveLift
open RhNativeCompleteBilinear RhFlatSmoothCore RhSmoothDerivativeDictionary

def physicalUnit (R : ℝ) : Set (FlatCoreSpace R) :=
  {F | ‖physicalEmbedding (F : WeightedSpace)‖ = 1}

def diagonal (R C : ℝ) (N : ℕ) (F : FlatCoreSpace R) : ℝ :=
  completeForm R C N (F : WeightedSpace) (F : WeightedSpace)

def bottom (R C : ℝ) (N : ℕ) : ℝ :=
  RhVariationalInfimum.ground (physicalUnit R) (diagonal R C N)

lemma derivative_lift_physical_ae {R : ℝ} (hR : 0 < R) {f : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hs : tsupport f ⊆ Ioo (-R) R) :
    physicalEmbedding (actualPrimitiveLift hR (deriv f) (derivative_memLp hf)) =ᵐ[volume]
      fun t => (f t : ℂ) := by
  rw [actualPrimitiveLift_physical]
  have hv : RhTail.physicalFourierVector R (primitive R (deriv f))
      (primitive_memLp (derivative_memLp hf)) =ᵐ[volume]
      RhTail.complexExtension R (primitive R (deriv f)) :=
    (RhTail.complexExtension_memLp (primitive_memLp (derivative_memLp hf))).coeFn_toLp
  filter_upwards [hv, primitive_derivative_ae hR hf hs] with t ht hp
  rw [ht]
  by_cases hi : t ∈ interval R
  · simp [RhTail.complexExtension, zeroExtension, hi, hp]
  · have hz : f t = 0 := by
      by_contra hn
      have hh := hs (subset_tsupport f hn)
      exact hi ⟨hh.1.le, hh.2.le⟩
    simp [RhTail.complexExtension, zeroExtension, hi, hz]

/-- The Rayleigh infimum ranges over a genuine nonempty physical unit set. -/
theorem physicalUnit_nonempty {R : ℝ} (hR : 0 < R) : (physicalUnit R).Nonempty := by
  let phi := RhActualCoreBump.centralBump R hR 0
  let f : ℝ → ℝ := phi.normed volume
  have hf : ContDiff ℝ ∞ f := phi.contDiff_normed
  have hs : tsupport f ⊆ Ioo (-R) R := RhActualCoreBump.normed_tsupport hR 0
  let F : FlatCoreSpace R := actualFlatCoreLift hR (deriv f) (derivative_memLp hf)
  have hAE : physicalEmbedding (F : WeightedSpace) =ᵐ[volume] fun t => (f t : ℂ) :=
    derivative_lift_physical_ae hR hf hs
  have hn : ‖physicalEmbedding (F : WeightedSpace)‖ ≠ 0 := by
    intro hz
    have hzero := (Lp.eq_zero_iff_ae_eq_zero).mp (norm_eq_zero.mp hz)
    have hfzero : f =ᵐ[volume] 0 := by
      filter_upwards [hAE, hzero] with t ht hz
      have hc : (f t : ℂ) = 0 := ht.symm.trans hz
      exact_mod_cast hc
    have hi : (∫ t, f t) = 0 := by
      rw [integral_congr_ae hfzero]
      simp
    have hmass : (∫ t, f t) = 1 := phi.integral_normed
    linarith
  have hp : 0 < ‖physicalEmbedding (F : WeightedSpace)‖ :=
    lt_of_le_of_ne (norm_nonneg _) (Ne.symm hn)
  refine ⟨(‖physicalEmbedding (F : WeightedSpace)‖⁻¹ : ℝ) • F, ?_⟩
  change ‖physicalEmbedding ((‖physicalEmbedding (F : WeightedSpace)‖⁻¹ : ℝ) • (F : WeightedSpace))‖ = 1
  rw [map_smul, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hp), inv_mul_cancel₀ hn]

lemma diagonal_lower_bound (R C : ℝ) (N : ℕ) (F : FlatCoreSpace R)
    (hF : F ∈ physicalUnit R) :
    -RhCompleteFormBound.boundConstant R C N ≤ diagonal R C N F := by
  have hb := RhNativeBoundedPartControl.boundedPart_mass_bound R C N (F : WeightedSpace)
  have ha := archPair_nonnegative (F : WeightedSpace)
  have hm : ‖physicalEmbedding (F : WeightedSpace)‖^2 = 1 := by rw [hF]; norm_num
  rw [hm, mul_one] at hb
  change _ ≤ archPair (F : WeightedSpace) (F : WeightedSpace) +
    boundedPart R C N (F : WeightedSpace) (F : WeightedSpace)
  linarith [(abs_le.mp hb).1]

theorem diagonal_bddBelow (R C : ℝ) (N : ℕ) :
    BddBelow ((diagonal R C N) '' physicalUnit R) := by
  refine ⟨-RhCompleteFormBound.boundConstant R C N, ?_⟩
  rintro y ⟨F,hF,rfl⟩
  exact diagonal_lower_bound R C N F hF

theorem bottom_le_diagonal (R C : ℝ) (N : ℕ) (F : FlatCoreSpace R)
    (hF : F ∈ physicalUnit R) : bottom R C N ≤ diagonal R C N F :=
  RhVariationalInfimum.ground_le (diagonal_bddBelow R C N) hF

end RhNativeRayleighDomain
#print axioms RhNativeRayleighDomain.physicalUnit_nonempty
#print axioms RhNativeRayleighDomain.diagonal_bddBelow
#print axioms RhNativeRayleighDomain.bottom_le_diagonal
