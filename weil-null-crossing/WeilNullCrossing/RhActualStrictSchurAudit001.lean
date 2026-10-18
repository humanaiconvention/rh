import RhLiteralSchurStrictSign001

/-! Terminal conditional zero-mode audit. Actual base positivity constructs
all nullspace/complement data. A strict outward step has negative Schur
energy in every nonzero old-null coordinate. Positivity can continue locally
exactly when the OLD radical dimension is zero. No actual zero-radius is
asserted and no all-radius positivity is proved. -/
noncomputable section
set_option maxHeartbeats 160000
set_option synthInstance.maxHeartbeats 20000
open Set MeasureTheory
open scoped Topology BigOperators
namespace RhActualStrictSchurAudit
open RhWeightedMeasureEmbedding RhFlatSmoothCore RhNativeCompleteBilinear
open RhPhysicalOrthogonalSchur RhPulledCompleteForm RhFixedPhysicalPulledSchur
open RhFixedPhysicalSchurMatrix RhInwardOldNullLift

theorem local_strict_schur_audit {R : ℝ} (hR : 0 < R) (C : ℝ) (N : ℕ)
    (hpos : ∀ F : FlatCoreSpace R,
      0 ≤ completeForm R C N (F : WeightedSpace) (F : WeightedSpace)) :
    ∃ (d : ℕ) (p : Fin d → FlatCoreSpace R) (mu : ℝ),
      Orthonormal ℝ (fun i => physicalEmbedding (p i : WeightedSpace)) ∧
      (∀ i, p i ∈ (baseForm R C N).ker) ∧
      (∀ z : FlatCoreSpace R, z ∈ (baseForm R C N).ker →
        ∃ c : Fin d → ℝ, z = ∑ i, c i • p i) ∧
      0 < mu ∧ PhysicalGap R C N p mu ∧
      ∃ delta > 0, ∀ (r : ℝ) (hr : 1 ≤ r), |r-1| < delta → 1 < r →
        let w : Fin d → FlatCoreSpace R := fun i => oldNullLift hR hr (p i)
        ∃ h : Control hr C N w (mu/2)
          ((((mu/2)/(mu/2+RhCompleteFormBound.boundConstant R C N+1)))/2),
          (∀ c : Fin d → ℝ, c ≠ 0 →
            ∑ i, ∑ j, c i*c j * schurMatrix hr C N w h i j < 0) ∧
          ((∀ F : FlatCoreSpace R, 0 ≤ pulledForm hr C N F F) ↔ d = 0) := by
  classical
  obtain ⟨d,p,mu,hp,hn,hspan,hmu,hgap,delta,hdelta,hlocal⟩ :=
    RhActualLiteralNullSchur.local_literal_null_schur_target hR C N hpos
  refine ⟨d,p,mu,hp,hn,hspan,hmu,hgap,delta,hdelta,?_⟩
  intro r hr hclose hrstrict
  obtain ⟨h,hzero,hentry,hnonpos,hcriterion⟩ := hlocal r hr hclose
  let w : Fin d → FlatCoreSpace R := fun i => oldNullLift hR hr (p i)
  have hw := RhOldNullPhysicalIsometry.physical_orthonormal hR hr p hp
  have hstrict (c : Fin d → ℝ) (hc : c ≠ 0) :
      ∑ i, ∑ j, c i*c j * schurMatrix hr C N w h i j < 0 :=
    RhLiteralSchurStrictSign.schur_quadratic_strictly_negative
      hR hr hrstrict C N p hp hzero h c hc
  refine ⟨h,hstrict,?_⟩
  constructor
  · intro hall
    by_contra hd
    have hdpos : 0 < d := Nat.pos_of_ne_zero hd
    let i : Fin d := ⟨0,hdpos⟩
    let c : Fin d → ℝ := fun j => if j=i then 1 else 0
    have hc : c ≠ 0 := by
      intro hz
      have hi := congrFun hz i
      norm_num [c] at hi
    have hn := hstrict c hc
    have hp := (RhPhysicalProjectionSchur.full_core_schur_iff hr C N w hw h).mp hall c
    linarith
  · intro hd
    apply hcriterion.mpr
    intro i
    have hi := i.isLt
    omega

end RhActualStrictSchurAudit
#print axioms RhActualStrictSchurAudit.local_strict_schur_audit
