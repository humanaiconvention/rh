import RhCompactPositiveSequence001

/-! Finite dimensionality of the actual radical of a positive complete graph
form with compact physical embedding. Positivity remains an explicit premise. -/
set_option maxHeartbeats 0
noncomputable section
open Filter Set
open scoped Topology
namespace RhCompactPositiveKernel
variable {V H : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- The nullspace is derived as the actual radical of the bounded form;
finite dimensionality is proved, not assumed. -/
theorem finite_nullspace (q : V →L[ℝ] V →L[ℝ] ℝ)
    (J : V →L[ℝ] H) (hJ : IsCompactOperator J)
    {G : ℝ} (hG : 0 ≤ G) (hq : ∀ x : V, 0 ≤ q x x)
    (hsym : ∀ x y : V, q x y = q y x)
    (hgraph : ∀ x : V, ‖x‖^2 ≤ q x x + G*‖J x‖^2) :
    FiniteDimensional ℝ q.ker := by
  let S : Set V := {x | x ∈ q.ker ∧ ‖x‖ ≤ 1}
  have hseq : IsSeqCompact S := by
    intro x hx
    have hb (n : ℕ) : ‖x n‖ ≤ 1 := (hx n).2
    have hzero (n : ℕ) : q (x n) (x n) = 0 :=
      (RhCompactPositiveSequence.radical_iff_zero_diagonal q hsym hq (x n)).mp (hx n).1
    have he : Tendsto (fun n => q (x n) (x n)) atTop (𝓝 0) := by
      simpa only [hzero] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
    obtain ⟨z,phi,hphi,ht,hz⟩ := RhCompactPositiveSequence.compact_zero_subsequence
      q J hJ hG hq hgraph x hb he
    have hzker : z ∈ q.ker :=
      (RhCompactPositiveSequence.radical_iff_zero_diagonal q hsym hq z).mpr hz
    have hznorm : ‖z‖ ≤ 1 := le_of_tendsto ht.norm (Eventually.of_forall (fun n => hb (phi n)))
    exact ⟨z,⟨hzker,hznorm⟩,phi,hphi,ht⟩
  have hS : IsCompact S := hseq.isCompact
  have hball : IsCompact (Metric.closedBall (0 : q.ker) 1) := by
    have hh := ((q.ker).isClosedEmbedding_subtype q.isClosed_ker).isCompact_preimage hS
    convert hh using 1
    ext x
    simp only [Metric.mem_closedBall, dist_zero_right, mem_preimage, S, mem_setOf_eq]
    change (‖x‖ ≤ 1) ↔ ((x : V) ∈ q.ker ∧ ‖x‖ ≤ 1)
    simp only [x.property, true_and]
  have hi : IsCompactOperator (id : q.ker → q.ker) := by
    apply (isCompactOperator_iff_image_closedBall_subset_compact
      (ContinuousLinearMap.id ℝ q.ker).toLinearMap (by norm_num : (0 : ℝ) < 1)).mpr
    exact ⟨Metric.closedBall 0 1,hball,by simp⟩
  exact (isCompactOperator_id_iff_finiteDimensional (𝕜 := ℝ)).mp hi

end RhCompactPositiveKernel
#print axioms RhCompactPositiveKernel.finite_nullspace


