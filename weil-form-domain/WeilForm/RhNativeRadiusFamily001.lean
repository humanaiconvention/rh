import RhNativeNoNullOpenness001
import RhCompleteFormHorizon001

/-! Actual all-prime support-radius family. A bounded neighborhood is EXACTLY
represented by one finite horizon before taking any limits. No infinite
prime sum or source spectral-continuity theorem is imported. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace RhNativeRadiusFamily
open RhAnchored RhWeightedMeasureEmbedding RhFlatSmoothCore RhNativeCompleteBilinear
open RhNativeRayleighDomain RhNativeRayleighRadius RhNativeRayleighPositivity
open RhNativeRayleighContinuity RhNativeCompactGap RhCompleteFormHorizon

def nativeBottom (R C : ℝ) : ℝ := bottom R C (RhAllPrime.radiusCutoff R)

lemma nativeBottom_fixed_cap {R S : ℝ} (hRS : R ≤ S) (C : ℝ) {N : ℕ}
    (hN : RhAllPrime.radiusCutoff S ≤ N) : nativeBottom R C = bottom R C N := by
  unfold nativeBottom bottom RhVariationalInfimum.ground
  congr 1
  ext y
  have he : ∀ F : FlatCoreSpace R,
      diagonal R C (RhAllPrime.radiusCutoff R) F = diagonal R C N F := by
    intro F
    exact bounded_radius_form_horizon hRS C hN
      (flatCore_supported R F.property) (flatCore_supported R F.property)
  simp only [he]

/-- Continuous native all-prime ground family, proved with a local FIXED cap. -/
theorem nativeBottom_continuousAt {R : ℝ} (hR : 0 < R) (C : ℝ) :
    ContinuousAt (fun S : ℝ => nativeBottom S C) R := by
  apply Metric.continuousAt_iff.mpr
  intro eps heps
  let cap := R+1
  let N := RhAllPrime.radiusCutoff cap
  obtain ⟨d,hd,hc⟩ := radius_neighborhood hR C N heps
  refine ⟨min 1 d,lt_min (by norm_num) hd,?_⟩
  intro S hS
  have hnear : |S-R| < min 1 d := by simpa only [Real.dist_eq] using hS
  have hScap : S ≤ cap := by
    have hh := (abs_lt.mp (hnear.trans_le (min_le_left _ _))).2
    dsimp only [cap]; linarith
  have hRcap : R ≤ cap := by dsimp only [cap]; linarith
  have hs := nativeBottom_fixed_cap hScap C (N:=N) le_rfl
  have hr := nativeBottom_fixed_cap hRcap C (N:=N) le_rfl
  rw [Real.dist_eq,hs,hr]
  exact hc S (hnear.trans_le (min_le_right _ _))

theorem nativeBottom_continuousOn (C : ℝ) :
    ContinuousOn (fun R : ℝ => nativeBottom R C) (Ioi 0) := by
  intro R hR
  exact (nativeBottom_continuousAt hR C).continuousWithinAt

/-- Native support inclusion lowers the ground value; this direction cannot
be used to propagate positivity from one radius to every larger radius. -/
theorem nativeBottom_antitone {R S : ℝ} (hR : 0 < R) (hRS : R ≤ S) (C : ℝ) :
    nativeBottom S C ≤ nativeBottom R C := by
  rw [nativeBottom_fixed_cap (R:=R) hRS C (N:=RhAllPrime.radiusCutoff S) le_rfl]
  exact bottom_antitone_support hR hRS C (RhAllPrime.radiusCutoff S)

/-- The native physical-kernel dictionary, with the EXACT native scalar. -/
theorem nativeBottom_nonnegative_iff_physical {R : ℝ} (hR : 0 < R) :
    0 ≤ nativeBottom R archConstant ↔
      ∀ v : ℝ → ℝ, MemLp v 2 (physicalMeasure R) →
        0 ≤ kernelQuadratic R (RhAllPrime.radiusKernel R) v := by
  exact (bottom_nonnegative_iff hR archConstant (RhAllPrime.radiusCutoff R)).trans
    (radius_physical_positive_iff_fixed_form_positive hR le_rfl).symm

/-- Actual native sign loss implies an actual nonzero finite-radius radical.
No endpoint sign or zero radius is asserted by this conditional theorem. -/
theorem native_sign_change_has_null {R0 R1 : ℝ} (hR0 : 0 < R0) (h01 : R0 ≤ R1)
    (C : ℝ) (hbase : 0 < nativeBottom R0 C) (hbad : nativeBottom R1 C < 0) :
    ∃ R : ℝ, R0 < R ∧ R < R1 ∧ nativeBottom R C = 0 ∧
      ∃ F : FlatCoreSpace R, F ≠ 0 ∧
        F ∈ (form R C (RhAllPrime.radiusCutoff R)).ker := by
  have hcont : ContinuousOn (fun R : ℝ => nativeBottom R C) (Icc R0 R1) :=
    (nativeBottom_continuousOn C).mono (by intro R hR; exact hR0.trans_le hR.1)
  obtain ⟨R,hR,hzero⟩ := intermediate_value_Icc' h01 hcont
    (show (0:ℝ) ∈ Icc (nativeBottom R1 C) (nativeBottom R0 C) from ⟨hbad.le,hbase.le⟩)
  have hR0ne : R ≠ R0 := by intro hh; subst R; linarith
  have hR1ne : R ≠ R1 := by intro hh; subst R; linarith
  have hleft : R0 < R := lt_of_le_of_ne hR.1 (Ne.symm hR0ne)
  have hright : R < R1 := lt_of_le_of_ne hR.2 hR1ne
  exact ⟨R,hleft,hright,hzero,
    zero_bottom_has_actual_null (hR0.trans hleft) C (RhAllPrime.radiusCutoff R) hzero⟩

end RhNativeRadiusFamily
#print axioms RhNativeRadiusFamily.nativeBottom_fixed_cap
#print axioms RhNativeRadiusFamily.nativeBottom_continuousAt
#print axioms RhNativeRadiusFamily.nativeBottom_antitone
#print axioms RhNativeRadiusFamily.nativeBottom_nonnegative_iff_physical
#print axioms RhNativeRadiusFamily.native_sign_change_has_null
