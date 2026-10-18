import RhRotatingPhysicalGap001
import RhPhysicalNullOverlap001
import RhNativeDilationSmallness001

/-! Actual local complement control for the INWARD old-null family. The finite
rotation error is proved to vanish from actual strong inward continuity;
no moving-family physical gap, overlap, or perturbation premise is assumed. -/
noncomputable section
set_option maxHeartbeats 150000
set_option synthInstance.maxHeartbeats 20000
open Set Filter MeasureTheory
open scoped Topology BigOperators
namespace RhActualRotatingLocalControl
open RhWeightedMeasureEmbedding RhFlatSmoothCore RhNativeCompleteBilinear
open RhPhysicalOrthogonalSchur RhPulledCompleteForm RhFixedPhysicalPulledSchur
open RhRotatingPhysicalGap RhInwardOldNullLift RhPhysicalNullOverlap

/-- The ACTUAL finite physical error, not a hypothesized rotation budget. -/
theorem rotationError_tendsto {d : ℕ} {R : ℝ} (hR : 0 < R)
    (p : Fin d → FlatCoreSpace R) :
    Tendsto (fun r : Scale => rotationError p (liftedFamily hR p r))
      (𝓝 oneScale) (𝓝 0) := by
  have hi (i : Fin d) : Tendsto (fun r : Scale =>
      ‖physicalEmbedding (p i : WeightedSpace) -
        physicalEmbedding (liftedFamily hR p r i : WeightedSpace)‖^2)
      (𝓝 oneScale) (𝓝 (0 : ℝ)) := by
    have hc : Tendsto (fun _ : Scale => physicalEmbedding (p i : WeightedSpace))
        (𝓝 oneScale) (𝓝 (physicalEmbedding (p i : WeightedSpace))) := tendsto_const_nhds
    have hh := (hc.sub (physical_lift_tendsto hR p i)).norm.pow 2
    simpa only [sub_self, norm_zero, zero_pow (by omega : (2 : ℕ) ≠ 0)] using hh
  have hs := tendsto_finset_sum Finset.univ (fun i hi' => hi i)
  simpa only [rotationError, Finset.sum_const_zero] using hs

lemma exists_local_rotation_bound {d : ℕ} {R : ℝ} (hR : 0 < R)
    (p : Fin d → FlatCoreSpace R) :
    ∃ delta > 0, ∀ r : Scale, |(r : ℝ)-1| < delta →
      rotationError p (liftedFamily hR p r) ≤ 1/2 := by
  have he : ∀ᶠ r : Scale in 𝓝 oneScale,
      rotationError p (liftedFamily hR p r) < 1/2 :=
    (rotationError_tendsto hR p).eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1/2))
  obtain ⟨delta,hdelta,hd⟩ := Metric.eventually_nhds_iff.mp he
  refine ⟨delta,hdelta,?_⟩
  intro r hclose
  have hs : dist r oneScale < delta := by
    simpa only [Subtype.dist_eq, Real.dist_eq, oneScale] using hclose
  exact (hd hs).le

/-- With one fixed radius and finite native horizon, actual rotating-family
Control exists on a genuine outward neighborhood. Only actual old-basis
orthonormality, old nullity, and the old positive physical gap are premises. -/
theorem exists_actual_local_control {d : ℕ} {R : ℝ} (hR : 0 < R)
    (C : ℝ) (N : ℕ) (p : Fin d → FlatCoreSpace R)
    (hp : Orthonormal ℝ (fun i => physicalEmbedding (p i : WeightedSpace)))
    (hn : ∀ i, p i ∈ (baseForm R C N).ker) {mu : ℝ}
    (hmu : 0 < mu) (hgap : PhysicalGap R C N p mu) :
    ∃ delta > 0, ∀ (r : ℝ) (hr : 1 ≤ r), |r-1| < delta →
      Control hr C N (fun i => oldNullLift hR hr (p i)) (mu/2)
        ((((mu/2) / (mu/2 + RhCompleteFormBound.boundConstant R C N + 1))) / 2) := by
  have hK := RhCompleteFormBound.boundConstant_nonneg R C N
  have ht : 0 < (mu/2) / (mu/2 + RhCompleteFormBound.boundConstant R C N + 1) := by
    positivity
  obtain ⟨dE,hdE,hE⟩ := exists_local_rotation_bound hR p
  obtain ⟨dB,hdB,hB⟩ :=
    RhNativeDilationSmallness.uniform_actual_graph_form_smallness hR C N (half_pos ht)
  let delta := min 1 (min dE dB)
  refine ⟨delta,lt_min (by norm_num) (lt_min hdE hdB),?_⟩
  intro r hr hclose
  have hone : |r-1| < 1 := hclose.trans_le (min_le_left _ _)
  have hr2 : r ≤ 2 := by have hh := (abs_lt.mp hone).2; linarith
  have hcloseE : |r-1| < dE :=
    hclose.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hcloseB : |r-1| < dB :=
    hclose.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  let s : Scale := ⟨r,hr,hr2⟩
  have hrotation : rotationError p (fun i => oldNullLift hR hr (p i)) ≤ 1/2 := by
    have heq : liftedFamily hR p s = (fun i => oldNullLift hR hr (p i)) := by
      funext i
      rfl
    rw [heq] at *
    exact hE s hcloseE
  apply rotatedControl hr C N p (fun i => oldNullLift hR hr (p i))
    hp hn hmu hgap hrotation
  · intro q
    have hb := hB r hr hcloseB
      (toCore R (fun i => oldNullLift hR hr (p i)) q)
    simpa only [toCore_norm] using hb
  · linarith

end RhActualRotatingLocalControl
#print axioms RhActualRotatingLocalControl.rotationError_tendsto
#print axioms RhActualRotatingLocalControl.exists_actual_local_control


