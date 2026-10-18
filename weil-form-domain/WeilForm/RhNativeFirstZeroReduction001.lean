import RhNativeRayleighContinuity001
import Mathlib.Topology.Order.IntermediateValue

/-! Exact finite-cap continuation criterion. These are CONDITIONAL reductions,
not proofs that actual null states are absent. All radii share ONE finite
prime horizon; separate native horizon coherence is needed for all-prime use. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace RhNativeFirstZeroReduction
open RhWeightedMeasureEmbedding RhFlatSmoothCore RhNativeCompleteBilinear
open RhNativeRayleighDomain RhNativeRayleighPositivity RhNativeRayleighContinuity
open RhNativeCompactGap

/-- A sign change forces an actual finite-radius zero and nonzero nullvector.
The theorem does not assert either endpoint sign for the native family. -/
theorem sign_change_has_actual_null {R0 R1 : ℝ} (hR0 : 0 < R0) (h01 : R0 ≤ R1)
    (C : ℝ) (N : ℕ) (hbase : 0 < bottom R0 C N) (hbad : bottom R1 C N < 0) :
    ∃ R : ℝ, R0 < R ∧ R < R1 ∧ bottom R C N = 0 ∧
      ∃ F : FlatCoreSpace R, F ≠ 0 ∧ F ∈ (form R C N).ker := by
  have hcont : ContinuousOn (fun R : ℝ => bottom R C N) (Icc R0 R1) :=
    (bottom_continuousOn C N).mono (by intro R hR; exact hR0.trans_le hR.1)
  obtain ⟨R,hR,hzero⟩ := intermediate_value_Icc' h01 hcont (show (0:ℝ) ∈
    Icc (bottom R1 C N) (bottom R0 C N) from ⟨hbad.le,hbase.le⟩)
  have hR0ne : R ≠ R0 := by intro hh; subst R; linarith
  have hR1ne : R ≠ R1 := by intro hh; subst R; linarith
  have hleft : R0 < R := lt_of_le_of_ne hR.1 (Ne.symm hR0ne)
  have hright : R < R1 := lt_of_le_of_ne hR.2 hR1ne
  exact ⟨R,hleft,hright,hzero,zero_bottom_has_actual_null (hR0.trans hleft) C N hzero⟩

/-- Precise missing alternative: ruling out actual radicals at every
nonnegative state in a finite radial cap rules out sign loss in that cap.
This hypothesis is NOT supplied by local coercivity or numerical margins. -/
theorem positivity_of_no_null_nonnegative_states {R0 Rmax : ℝ} (hR0 : 0 < R0)
    (hcap : R0 ≤ Rmax) (C : ℝ) (N : ℕ) (hbase : 0 < bottom R0 C N)
    (hno : ∀ R ∈ Ioc R0 Rmax,
      (∀ F : FlatCoreSpace R,
        0 ≤ completeForm R C N (F : WeightedSpace) (F : WeightedSpace)) →
      ∀ F : FlatCoreSpace R, F ∈ (form R C N).ker → F = 0) :
    ∀ R ∈ Icc R0 Rmax, ∀ F : FlatCoreSpace R,
      0 ≤ completeForm R C N (F : WeightedSpace) (F : WeightedSpace) := by
  intro R hR
  apply (bottom_nonnegative_iff (hR0.trans_le hR.1) C N).mp
  by_contra hh
  have hbad := lt_of_not_ge hh
  obtain ⟨S,hS0,hSR,hzero,F,hF,hker⟩ :=
    sign_change_has_actual_null hR0 hR.1 C N hbase hbad
  have hpos := (bottom_nonnegative_iff (hR0.trans hS0) C N).mp hzero.ge
  exact hF (hno S ⟨hS0,(hSR.le.trans hR.2)⟩ hpos F hker)

end RhNativeFirstZeroReduction
#print axioms RhNativeFirstZeroReduction.sign_change_has_actual_null
#print axioms RhNativeFirstZeroReduction.positivity_of_no_null_nonnegative_states
