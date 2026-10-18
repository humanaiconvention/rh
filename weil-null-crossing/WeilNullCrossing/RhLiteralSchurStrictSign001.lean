import RhActualLiteralNullSchur001
import RhNativeStrictInteriorUCP001

/-! Strict outward Schur sign on the literal OLD physical null family.
No zero state is asserted to exist. A given complement Control supplies its
actual inverse; complete strict-interior UCP forces every nonzero full source
combination to survive. No individual arithmetic component is estimated. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 25000
open Set MeasureTheory
open scoped Topology BigOperators
namespace RhLiteralSchurStrictSign
open RhWeightedMeasureEmbedding RhFlatSmoothCore RhNativeCompleteBilinear
open RhPhysicalOrthogonalSchur RhPulledCompleteForm RhFixedPhysicalPulledSchur
open RhFixedPhysicalSchurMatrix RhPhysicalProjectionSchur RhInwardOldNullLift

lemma row_zero_of_zero_source {d : ℕ} {R r : ℝ} (hr : 1 ≤ r)
    (C : ℝ) (N : ℕ) (w : Fin d → FlatCoreSpace R)
    (hw : Orthonormal ℝ (fun i => physicalEmbedding (w i : WeightedSpace)))
    (hzero : ∀ i j, pulledForm hr C N (w i) (w j) = 0)
    (c : Fin d → ℝ) (hb : crossSource hr C N w (combination w c) = 0) :
    ∀ F : FlatCoreSpace R, pulledForm hr C N (combination w c) F = 0 := by
  intro F
  have hlo : pulledForm hr C N (combination w c) (projection w F) = 0 := by
    simp only [projection,combination,map_sum,map_smul,
      ContinuousLinearMap.sum_apply,ContinuousLinearMap.smul_apply,smul_eq_mul]
    simp only [hzero,mul_zero,Finset.sum_const_zero]
  have hhi : pulledForm hr C N (combination w c) (toCore R w (remainder w hw F)) = 0 := by
    rw [← RhFixedPhysicalPulledSchur.crossSource_weak,hb,inner_zero_left]
  calc
    _ = pulledForm hr C N (combination w c)
        (projection w F + toCore R w (remainder w hw F)) := by rw [physical_decomposition]
    _ = 0 := by rw [map_add,hlo,hhi,add_zero]

lemma outward_combination_literal {d : ℕ} {R r : ℝ}
    (hR : 0 < R) (hr : 1 ≤ r) (p : Fin d → FlatCoreSpace R) (c : Fin d → ℝ) :
    (RhFlatCoreDilation.outwardMap hr
      (combination (fun i => oldNullLift hR hr (p i)) c) : WeightedSpace) =
        (combination p c : WeightedSpace) := by
  calc
    _ = ∑ i, c i • (RhFlatCoreDilation.outwardMap hr (oldNullLift hR hr (p i)) : WeightedSpace) := by
      simp [combination]
    _ = ∑ i, c i • (p i : WeightedSpace) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [outward_oldNullLift_ambient]
    _ = _ := by simp [combination]

/-- Every nonzero coordinate has a nonzero FULL complement source. Both
support radii are genuine and strict; no old null existence is inferred. -/
theorem source_combination_ne_zero {d : ℕ} {R r : ℝ}
    (hR : 0 < R) (hr : 1 ≤ r) (hrstrict : 1 < r) (C : ℝ) (N : ℕ)
    (p : Fin d → FlatCoreSpace R)
    (hp : Orthonormal ℝ (fun i => physicalEmbedding (p i : WeightedSpace)))
    (hzero : ∀ i j, pulledForm hr C N (oldNullLift hR hr (p i))
      (oldNullLift hR hr (p j)) = 0)
    (c : Fin d → ℝ) (hc : c ≠ 0) :
    crossSource hr C N (fun i => oldNullLift hR hr (p i))
      (combination (fun i => oldNullLift hR hr (p i)) c) ≠ 0 := by
  intro hb
  let w : Fin d → FlatCoreSpace R := fun i => oldNullLift hR hr (p i)
  have hw := RhOldNullPhysicalIsometry.physical_orthonormal hR hr p hp
  have hrow := row_zero_of_zero_source hr C N w hw hzero c hb
  have hRS : R < r*R := by nlinarith
  have hfull (G : FlatCoreSpace (r*R)) :
      completeForm (r*R) C N (combination p c : WeightedSpace) (G : WeightedSpace) = 0 := by
    have hh := hrow (RhFlatCoreDilation.returnMap hr G)
    rw [pulledForm_apply, outward_combination_literal hR hr p c] at hh
    have hG := congrArg (fun X : FlatCoreSpace (r*R) => (X : WeightedSpace))
      (RhFlatCoreDilation.outward_return_cancel hr G)
    rw [hG] at hh
    exact hh
  have hz := RhNativeStrictInteriorUCP.full_row_unique hR hRS C N (combination p c) hfull
  apply hc
  have hcoords := coefficients_combination p hp c
  rw [hz] at hcoords
  funext i
  have hi := congrFun hcoords i
  simpa [coefficients] using hi.symm

/-- Exact strict negative definiteness on every nonzero old-null coordinate,
provided the ACTUAL full complement inverse is available locally. -/
theorem schur_quadratic_strictly_negative {d : ℕ} {R r : ℝ}
    (hR : 0 < R) (hr : 1 ≤ r) (hrstrict : 1 < r) (C : ℝ) (N : ℕ)
    (p : Fin d → FlatCoreSpace R)
    (hp : Orthonormal ℝ (fun i => physicalEmbedding (p i : WeightedSpace)))
    (hzero : ∀ i j, pulledForm hr C N (oldNullLift hR hr (p i))
      (oldNullLift hR hr (p j)) = 0)
    {mu eta : ℝ}
    (h : Control hr C N (fun i => oldNullLift hR hr (p i)) mu eta)
    (c : Fin d → ℝ) (hc : c ≠ 0) :
    ∑ i, ∑ j, c i*c j *
      schurMatrix hr C N (fun i => oldNullLift hR hr (p i)) h i j < 0 := by
  let w : Fin d → FlatCoreSpace R := fun i => oldNullLift hR hr (p i)
  let v := combination w c
  have hb := source_combination_ne_zero hR hr hrstrict C N p hp hzero c hc
  have hn := payment_nonnegative hr C N w h v
  have hne : inner ℝ (crossSource hr C N w v)
      (inverse hr C N w h (crossSource hr C N w v)) ≠ 0 := by
    intro hz
    exact hb ((RhLiteralZeroBlockSchur.payment_zero_iff hr C N w h _).mp hz)
  have hpos : 0 < inner ℝ (crossSource hr C N w v)
      (inverse hr C N w h (crossSource hr C N w v)) := lt_of_le_of_ne hn (Ne.symm hne)
  have hv : pulledForm hr C N v v = 0 := by
    rw [form_combination]
    simp only [w,hzero,mul_zero,Finset.sum_const_zero]
  rw [← residual_combination]
  change pulledForm hr C N v v - inner ℝ (crossSource hr C N w v)
      (inverse hr C N w h (crossSource hr C N w v)) < 0
  rw [hv,zero_sub]
  exact neg_neg_of_pos hpos

end RhLiteralSchurStrictSign
#print axioms RhLiteralSchurStrictSign.row_zero_of_zero_source
#print axioms RhLiteralSchurStrictSign.outward_combination_literal
#print axioms RhLiteralSchurStrictSign.source_combination_ne_zero
#print axioms RhLiteralSchurStrictSign.schur_quadratic_strictly_negative
