import RhPositiveGraphCauchy001
import Mathlib.Topology.Sequences

/-! Compact physical embeddings promote bounded vanishing-energy sequences
into actual strong graph-convergent subsequences. Positivity remains explicit. -/
set_option maxHeartbeats 0
noncomputable section
open Filter Set
open scoped Topology
namespace RhCompactPositiveSequence
variable {V H : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- No weak-limit or lower-semicontinuity premise occurs in this theorem. -/
theorem compact_zero_subsequence (q : V →L[ℝ] V →L[ℝ] ℝ)
    (J : V →L[ℝ] H) (hJ : IsCompactOperator J)
    {G : ℝ} (hG : 0 ≤ G) (hq : ∀ x : V, 0 ≤ q x x)
    (hgraph : ∀ x : V, ‖x‖^2 ≤ q x x + G*‖J x‖^2)
    (x : ℕ → V) {C : ℝ} (hb : ∀ n, ‖x n‖ ≤ C)
    (he : Tendsto (fun n => q (x n) (x n)) atTop (𝓝 0)) :
    ∃ (z : V) (phi : ℕ → ℕ), StrictMono phi ∧
      Tendsto (x ∘ phi) atTop (𝓝 z) ∧ q z z = 0 := by
  obtain ⟨K,hK,himage⟩ := hJ.image_closedBall_subset_compact C
  have hmem (n : ℕ) : J (x n) ∈ K := by
    apply himage
    refine ⟨x n, ?_, rfl⟩
    simpa only [Metric.mem_closedBall, dist_zero_right] using hb n
  obtain ⟨y,_hy,phi,hphi,ht⟩ := hK.tendsto_subseq hmem
  have he' : Tendsto (fun n => q ((x ∘ phi) n) ((x ∘ phi) n)) atTop (𝓝 0) :=
    he.comp hphi.tendsto_atTop
  have hc : CauchySeq (fun n => J ((x ∘ phi) n)) := ht.cauchySeq
  obtain ⟨z,hz,hzero⟩ := RhPositiveGraphCauchy.graph_limit q J hG hq hgraph
    (x ∘ phi) he' hc
  exact ⟨z,phi,hphi,hz,hzero⟩

/-- For a symmetric positive form, a zero diagonal vector is a true radical
vector. The scalar parameter is constructed explicitly. -/
theorem zero_diagonal_radical (q : V →L[ℝ] V →L[ℝ] ℝ)
    (hsym : ∀ x y : V, q x y = q y x) (hq : ∀ x : V, 0 ≤ q x x)
    {x : V} (hx : q x x = 0) : q x = 0 := by
  apply ContinuousLinearMap.ext
  intro y
  by_contra hn
  have hxy : q x y ≠ 0 := by simpa only [ContinuousLinearMap.zero_apply] using hn
  let t : ℝ := (-q y y - 1)/(2*q x y)
  have hval : q (t • x + y) (t • x + y) = -1 := by
    simp only [map_add, map_smul, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply, smul_eq_mul]
    rw [hx, ← hsym x y]
    dsimp only [t]
    field_simp
    <;> ring
  have hp := hq (t • x + y)
  rw [hval] at hp
  norm_num at hp

lemma radical_iff_zero_diagonal (q : V →L[ℝ] V →L[ℝ] ℝ)
    (hsym : ∀ x y : V, q x y = q y x) (hq : ∀ x : V, 0 ≤ q x x) (x : V) :
    x ∈ q.ker ↔ q x x = 0 := by
  constructor
  · intro hx
    change q x = 0 at hx
    rw [hx]
    rfl
  · intro hx
    exact zero_diagonal_radical q hsym hq hx

end RhCompactPositiveSequence
#print axioms RhCompactPositiveSequence.compact_zero_subsequence
#print axioms RhCompactPositiveSequence.zero_diagonal_radical
#print axioms RhCompactPositiveSequence.radical_iff_zero_diagonal
