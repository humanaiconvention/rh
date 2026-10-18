import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Topology.Algebra.Support

/-! Private literal smooth splitting at two absent support points.
This is finite calculus only. No weighted-domain or arithmetic sign premise.
-/
set_option maxHeartbeats 150000
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace RhThreePieceSmoothSplit

def leftCut (c : ℝ) (f : ℝ → ℝ) (t : ℝ) : ℝ := if t < c then f t else 0
def rightCut (c : ℝ) (f : ℝ → ℝ) (t : ℝ) : ℝ := if c < t then f t else 0

lemma leftCut_tsupport_subset (c : ℝ) (f : ℝ → ℝ) :
    tsupport (leftCut c f) ⊆ tsupport f := by
  apply closure_mono
  intro t ht
  simp only [Function.mem_support, leftCut] at ht ⊢
  split_ifs at ht with h
  · exact ht
  · exact (ht rfl).elim

lemma rightCut_tsupport_subset (c : ℝ) (f : ℝ → ℝ) :
    tsupport (rightCut c f) ⊆ tsupport f := by
  apply closure_mono
  intro t ht
  simp only [Function.mem_support, rightCut] at ht ⊢
  split_ifs at ht with h
  · exact ht
  · exact (ht rfl).elim

lemma leftCut_contDiff (c : ℝ) (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f)
    (hc : c ∉ tsupport f) : ContDiff ℝ ∞ (leftCut c f) := by
  apply contDiff_iff_contDiffAt.mpr
  intro t
  rcases lt_trichotomy t c with ht | heq | ht
  · apply hf.contDiffAt.congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds ht] with u hu
    have hu' : u < c := hu
    simp only [leftCut, if_pos hu']
  · subst t
    have hz : f =ᶠ[𝓝 c] 0 := notMem_tsupport_iff_eventuallyEq.mp hc
    apply (contDiff_const : ContDiff ℝ ∞ (fun _ : ℝ => (0 : ℝ))).contDiffAt.congr_of_eventuallyEq
    filter_upwards [hz] with u hu
    simp only [leftCut, hu, Pi.zero_apply, ite_self]
  · apply (contDiff_const : ContDiff ℝ ∞ (fun _ : ℝ => (0 : ℝ))).contDiffAt.congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds ht] with u hu
    have hu' : c < u := hu
    simp only [leftCut, if_neg (not_lt.mpr hu'.le)]

lemma rightCut_contDiff (c : ℝ) (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f)
    (hc : c ∉ tsupport f) : ContDiff ℝ ∞ (rightCut c f) := by
  apply contDiff_iff_contDiffAt.mpr
  intro t
  rcases lt_trichotomy t c with ht | heq | ht
  · apply (contDiff_const : ContDiff ℝ ∞ (fun _ : ℝ => (0 : ℝ))).contDiffAt.congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds ht] with u hu
    have hu' : u < c := hu
    simp only [rightCut, if_neg (not_lt.mpr hu'.le)]
  · subst t
    have hz : f =ᶠ[𝓝 c] 0 := notMem_tsupport_iff_eventuallyEq.mp hc
    apply (contDiff_const : ContDiff ℝ ∞ (fun _ : ℝ => (0 : ℝ))).contDiffAt.congr_of_eventuallyEq
    filter_upwards [hz] with u hu
    simp only [rightCut, hu, Pi.zero_apply, ite_self]
  · apply hf.contDiffAt.congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds ht] with u hu
    have hu' : c < u := hu
    simp only [rightCut, if_pos hu']

lemma leftCut_strict_support (c : ℝ) (f : ℝ → ℝ) (hc : c ∉ tsupport f) :
    tsupport (leftCut c f) ⊆ Iio c := by
  have hclosed : tsupport (leftCut c f) ⊆ Iic c := by
    apply closure_minimal _ isClosed_Iic
    intro t ht
    by_contra h
    have hct : c < t := lt_of_not_ge h
    have hn : ¬t < c := not_lt.mpr hct.le
    exact ht (by simp only [leftCut, if_neg hn])
  intro t ht
  have hle : t ≤ c := hclosed ht
  exact lt_of_le_of_ne hle (fun he => hc (he ▸ leftCut_tsupport_subset c f ht))

lemma rightCut_strict_support (c : ℝ) (f : ℝ → ℝ) (hc : c ∉ tsupport f) :
    tsupport (rightCut c f) ⊆ Ioi c := by
  have hclosed : tsupport (rightCut c f) ⊆ Ici c := by
    apply closure_minimal _ isClosed_Ici
    intro t ht
    by_contra h
    have htc : t < c := lt_of_not_ge h
    have hn : ¬c < t := not_lt.mpr htc.le
    exact ht (by simp only [rightCut, if_neg hn])
  intro t ht
  have hle : c ≤ t := hclosed ht
  exact lt_of_le_of_ne hle (fun he => hc (he ▸ rightCut_tsupport_subset c f ht))

lemma leftCut_compact (c : ℝ) (f : ℝ → ℝ) (hc : HasCompactSupport f) :
    HasCompactSupport (leftCut c f) := by
  apply hc.mono'
  intro t ht
  exact leftCut_tsupport_subset c f (subset_tsupport _ ht)

lemma rightCut_compact (c : ℝ) (f : ℝ → ℝ) (hc : HasCompactSupport f) :
    HasCompactSupport (rightCut c f) := by
  apply hc.mono'
  intro t ht
  exact rightCut_tsupport_subset c f (subset_tsupport _ ht)

def leftPiece (R : ℝ) (f : ℝ → ℝ) : ℝ → ℝ := leftCut (-R) f
def middlePiece (R : ℝ) (f : ℝ → ℝ) : ℝ → ℝ := rightCut (-R) (leftCut R f)
def rightPiece (R : ℝ) (f : ℝ → ℝ) : ℝ → ℝ := rightCut R f

/-- Exact pointwise partition, including both cut points. -/
theorem pieces_sum (R : ℝ) (hR : 0 < R) (f : ℝ → ℝ)
    (hm : -R ∉ tsupport f) (hp : R ∉ tsupport f) (t : ℝ) :
    leftPiece R f t + middlePiece R f t + rightPiece R f t = f t := by
  have hfm : f (-R) = 0 := image_eq_zero_of_notMem_tsupport hm
  have hfp : f R = 0 := image_eq_zero_of_notMem_tsupport hp
  rcases lt_trichotomy t (-R) with ht | rfl | ht
  · have htr : t < R := by linarith
    simp [leftPiece, middlePiece, rightPiece, leftCut, rightCut, ht, htr, not_lt.mpr ht.le,
      not_lt.mpr htr.le]
  · simp [leftPiece, middlePiece, rightPiece, leftCut, rightCut, hfm, neg_lt_self hR]
  · rcases lt_trichotomy t R with ht' | rfl | ht'
    · simp [leftPiece, middlePiece, rightPiece, leftCut, rightCut, ht, ht', not_lt.mpr ht.le,
        not_lt.mpr ht'.le]
    · simp [leftPiece, middlePiece, rightPiece, leftCut, rightCut, hfp, neg_lt_self hR]
    · have htm : -R < t := ht
      simp [leftPiece, middlePiece, rightPiece, leftCut, rightCut, ht, ht', not_lt.mpr ht.le,
        not_lt.mpr ht'.le]

/-- Literal three smooth compact pieces with strict open supports. -/
theorem three_piece_split (R S : ℝ) (hR : 0 < R) (f : ℝ → ℝ)
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (hs : tsupport f ⊆ Ioo (-S) S)
    (hm : -R ∉ tsupport f) (hp : R ∉ tsupport f) :
    ContDiff ℝ ∞ (leftPiece R f) ∧ HasCompactSupport (leftPiece R f) ∧
    tsupport (leftPiece R f) ⊆ Ioo (-S) (-R) ∧
    ContDiff ℝ ∞ (middlePiece R f) ∧ HasCompactSupport (middlePiece R f) ∧
    tsupport (middlePiece R f) ⊆ Ioo (-R) R ∧
    ContDiff ℝ ∞ (rightPiece R f) ∧ HasCompactSupport (rightPiece R f) ∧
    tsupport (rightPiece R f) ⊆ Ioo R S ∧
    (∀t, leftPiece R f t + middlePiece R f t + rightPiece R f t = f t) := by
  have hml : -R ∉ tsupport (leftCut R f) :=
    fun h => hm (leftCut_tsupport_subset R f h)
  refine ⟨leftCut_contDiff (-R) f hf hm, leftCut_compact (-R) f hc, ?_,
    rightCut_contDiff (-R) (leftCut R f) (leftCut_contDiff R f hf hp) hml,
    rightCut_compact (-R) (leftCut R f) (leftCut_compact R f hc), ?_,
    rightCut_contDiff R f hf hp, rightCut_compact R f hc, ?_, pieces_sum R hR f hm hp⟩
  · intro t ht
    exact ⟨(hs (leftCut_tsupport_subset (-R) f ht)).1, leftCut_strict_support (-R) f hm ht⟩
  · intro t ht
    exact ⟨rightCut_strict_support (-R) (leftCut R f) hml ht,
      leftCut_strict_support R f hp (rightCut_tsupport_subset (-R) (leftCut R f) ht)⟩
  · intro t ht
    exact ⟨rightCut_strict_support R f hp ht, (hs (rightCut_tsupport_subset R f ht)).2⟩

end RhThreePieceSmoothSplit
#print axioms RhThreePieceSmoothSplit.leftCut_contDiff
#print axioms RhThreePieceSmoothSplit.rightCut_contDiff
#print axioms RhThreePieceSmoothSplit.leftCut_strict_support
#print axioms RhThreePieceSmoothSplit.rightCut_strict_support
#print axioms RhThreePieceSmoothSplit.pieces_sum
#print axioms RhThreePieceSmoothSplit.three_piece_split
