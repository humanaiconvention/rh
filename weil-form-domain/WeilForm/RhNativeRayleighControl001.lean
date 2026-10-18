import RhNativeRayleighDomain001
import RhNativeDilationSmallness001
import RhNativeGraphCoercivity001

/-! Actual local Rayleigh continuity in primitive PHYSICAL L2 normalization.
No lower sign, renewable margin, or derivative-input coercivity follows.
The finite prime horizon is fixed before the dilation neighborhood. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace RhNativeRayleighControl
open RhAnchored RhWeightedMeasureEmbedding RhFlatSmoothCore RhNativeCompleteBilinear
open RhPulledCompleteForm RhNativeRayleighDomain RhVariationalInfimum

def pulledDiagonal {R r : ℝ} (hr : 1 ≤ r) (C : ℝ) (N : ℕ)
    (F : FlatCoreSpace R) : ℝ := pulledForm hr C N F F

def pulledBottom {R r : ℝ} (hr : 1 ≤ r) (C : ℝ) (N : ℕ) : ℝ :=
  ground (physicalUnit R) (pulledDiagonal hr C N)

/-- Quantitative ground-value transfer from the genuine complete-form bound. -/
theorem local_ground_bound {R : ℝ} (hR : 0 < R) (C : ℝ) (N : ℕ)
    {eta : ℝ} (he0 : 0 < eta) (he1 : eta < 1) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ (r : ℝ) (hr : 1 ≤ r), |r-1| < delta →
      BddBelow ((pulledDiagonal (R:=R) hr C N) '' physicalUnit R) ∧
      |pulledBottom (R:=R) hr C N-bottom R C N| ≤
        eta*(|bottom R C N|+RhCompleteFormBound.boundConstant R C N+1) := by
  obtain ⟨delta,hd,hsmall⟩ :=
    RhNativeDilationSmallness.uniform_actual_graph_form_smallness hR C N he0
  refine ⟨delta,hd,?_⟩
  intro r hr hclose
  have hgraph : ∀ F ∈ physicalUnit R,
      ‖F‖^2 ≤ diagonal R C N F+(RhCompleteFormBound.boundConstant R C N+1) := by
    intro F hF
    have hh := RhNativeGraphCoercivity.native_graph_control R C N (F : WeightedSpace)
    have hm : ‖physicalEmbedding (F : WeightedSpace)‖^2 = 1 := by rw [hF]; norm_num
    rw [hm,mul_one] at hh
    exact hh
  have hp : ∀ F ∈ physicalUnit R,
      |pulledDiagonal hr C N F-diagonal R C N F| ≤ eta*‖F‖^2 := by
    intro F _hF
    change |pulledForm hr C N F F-baseForm R C N F F| ≤ eta*‖F‖^2
    rw [←differenceForm_apply]
    exact hsmall r hr hclose F
  have hh := graph_perturbation_ground_bound (physicalUnit_nonempty hR)
    (diagonal_bddBelow R C N) he0.le he1 hgraph hp
  simpa only [bottom,pulledBottom,add_assoc] using hh

/-- Exact epsilon neighborhood, not a numerical or finite-grid observation. -/
theorem local_ground_continuity {R : ℝ} (hR : 0 < R) (C : ℝ) (N : ℕ)
    {eps : ℝ} (heps : 0 < eps) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ (r : ℝ) (hr : 1 ≤ r), |r-1| < delta →
      |pulledBottom (R:=R) hr C N-bottom R C N| < eps := by
  let P := |bottom R C N|+RhCompleteFormBound.boundConstant R C N+1
  have hP : 0 < P := by
    have hK := RhCompleteFormBound.boundConstant_nonneg R C N
    dsimp only [P]
    positivity
  let eta := min (1/2 : ℝ) (eps/(2*P))
  have he0 : 0 < eta := lt_min (by norm_num) (by positivity)
  have he1 : eta < 1 := (min_le_left _ _).trans_lt (by norm_num)
  obtain ⟨delta,hd,hbound⟩ := local_ground_bound hR C N he0 he1
  refine ⟨delta,hd,?_⟩
  intro r hr hclose
  have hh := (hbound r hr hclose).2
  have hpay : eta*P ≤ eps/2 := by
    calc
      _ ≤ (eps/(2*P))*P := mul_le_mul_of_nonneg_right (min_le_right _ _) hP.le
      _ = _ := by field_simp
  exact hh.trans_lt (hpay.trans_lt (by linarith))

end RhNativeRayleighControl
#print axioms RhNativeRayleighControl.local_ground_bound
#print axioms RhNativeRayleighControl.local_ground_continuity
