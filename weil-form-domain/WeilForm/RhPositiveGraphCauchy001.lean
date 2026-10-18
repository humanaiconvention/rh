import RhSupportedCompactEmbedding001
import RhNativeGraphCoercivity001
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps

/-! A positive form plus a compact physical embedding yields strong graph
convergence for small-energy sequences. Positivity is an explicit hypothesis.
No arithmetic cancellation or zero-mode residual sign is asserted. -/
set_option maxHeartbeats 0
noncomputable section
open Filter Set
open scoped Topology
namespace RhPositiveGraphCauchy
variable {V H : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

lemma form_parallelogram (q : V →L[ℝ] V →L[ℝ] ℝ) (x y : V) :
    q (x-y) (x-y) + q (x+y) (x+y) = 2*q x x + 2*q y y := by
  simp only [map_add, map_sub, ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply]
  ring

lemma positive_difference (q : V →L[ℝ] V →L[ℝ] ℝ)
    (hq : ∀ x : V, 0 ≤ q x x) (x y : V) :
    q (x-y) (x-y) ≤ 2*q x x + 2*q y y := by
  linarith [form_parallelogram q x y, hq (x+y)]

/-- Physical Cauchy convergence and vanishing positive form energy force
Cauchy convergence in the COMPLETE graph norm. -/
theorem graph_cauchy (q : V →L[ℝ] V →L[ℝ] ℝ)
    (J : V →L[ℝ] H) {G : ℝ} (hG : 0 ≤ G)
    (hq : ∀ x : V, 0 ≤ q x x)
    (hgraph : ∀ x : V, ‖x‖^2 ≤ q x x + G*‖J x‖^2)
    (x : ℕ → V) (he : Tendsto (fun n => q (x n) (x n)) atTop (𝓝 0))
    (hc : CauchySeq (fun n => J (x n))) : CauchySeq x := by
  apply Metric.cauchySeq_iff.mpr
  intro eps heps
  have hs : 0 < eps^2/8 := by positivity
  obtain ⟨Nq,hNq⟩ := eventually_atTop.mp (he.eventually (eventually_lt_nhds hs))
  have hdelta : 0 < eps/(2*(G+1)) := by positivity
  obtain ⟨Nh,hNh⟩ := Metric.cauchySeq_iff.mp hc _ hdelta
  refine ⟨max Nq Nh, ?_⟩
  intro m hm n hn
  have hqm := hNq m ((le_max_left _ _).trans hm)
  have hqn := hNq n ((le_max_left _ _).trans hn)
  have hphys := hNh m ((le_max_right _ _).trans hm) n ((le_max_right _ _).trans hn)
  have hsmall : 2*(G+1)*dist (J (x m)) (J (x n)) < eps := by
    have hh := (lt_div_iff₀ (by positivity : 0 < 2*(G+1))).mp hphys
    simpa only [mul_comm] using hh
  have hsquare : (2*(G+1)*dist (J (x m)) (J (x n)))^2 < eps^2 :=
    (sq_lt_sq₀ (by positivity) heps.le).mpr hsmall
  have hGsquare : G ≤ (G+1)^2 := by nlinarith [sq_nonneg G]
  have hpaid := mul_le_mul_of_nonneg_right hGsquare
    (sq_nonneg (dist (J (x m)) (J (x n))))
  have hdiff := positive_difference q hq (x m) (x n)
  have hbound := hgraph (x m - x n)
  rw [J.map_sub (x m) (x n)] at hbound
  simp only [← dist_eq_norm] at hbound
  have hdnonneg := dist_nonneg (x := x m) (y := x n)
  nlinarith

/-- Completeness gives a strong graph limit; no weak topology is imported. -/
theorem graph_limit [CompleteSpace V] (q : V →L[ℝ] V →L[ℝ] ℝ)
    (J : V →L[ℝ] H) {G : ℝ} (hG : 0 ≤ G)
    (hq : ∀ x : V, 0 ≤ q x x)
    (hgraph : ∀ x : V, ‖x‖^2 ≤ q x x + G*‖J x‖^2)
    (x : ℕ → V) (he : Tendsto (fun n => q (x n) (x n)) atTop (𝓝 0))
    (hc : CauchySeq (fun n => J (x n))) :
    ∃ z : V, Tendsto x atTop (𝓝 z) ∧ q z z = 0 := by
  obtain ⟨z,hz⟩ := cauchySeq_tendsto_of_complete (graph_cauchy q J hG hq hgraph x he hc)
  refine ⟨z,hz,?_⟩
  have hcont : Continuous (fun y : V => q y y) := q.continuous.clm_apply continuous_id
  exact tendsto_nhds_unique (hcont.tendsto z |>.comp hz) he

end RhPositiveGraphCauchy
#print axioms RhPositiveGraphCauchy.positive_difference
#print axioms RhPositiveGraphCauchy.graph_cauchy
#print axioms RhPositiveGraphCauchy.graph_limit

