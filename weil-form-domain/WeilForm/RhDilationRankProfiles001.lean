import RhDilationRankL2001

noncomputable section
open Set MeasureTheory Filter
open scoped Topology BigOperators

namespace RhDilationRank
open RhAnchored

def profile (f : ℝ → ℝ) (r t : ℝ) : ℝ := Real.sqrt r * f (r * t / 2)
def coshProfile (r t : ℝ) : ℝ := profile Real.cosh r t
def sinhProfile (r t : ℝ) : ℝ := profile Real.sinh r t

lemma profile_continuous {f : ℝ → ℝ} (hf : Continuous f) (r : ℝ) :
    Continuous (profile f r) := by
  unfold profile
  exact continuous_const.mul (hf.comp (by fun_prop))

lemma profile_memLp {A r : ℝ} {f : ℝ → ℝ} (hf : Continuous f) :
    MemLp (profile f r) 2 (physicalMeasure A) :=
  continuous_memLp (profile_continuous hf r)

/-- Genuine common compact-profile bounds, with no assumed parameter continuity. -/
theorem exists_profile_bounds {A : ℝ} (hA : 0 < A) {f : ℝ → ℝ}
    (hf : ContDiff ℝ 1 f) :
    ∃ B : ℝ, 0 < B ∧ ∃ K : ℝ, 0 < K ∧
      ∀ r : ℝ, 1 ≤ r → r ≤ 2 → ∀ t ∈ interval A,
        |profile f r t| ≤ B ∧ |profile f r t - profile f 1 t| ≤ K * (r - 1) := by
  let X : Set (ℝ × ℝ) := Icc (1 : ℝ) 2 ×ˢ interval A
  have hcd : ContDiffOn ℝ 1 (fun p : ℝ × ℝ => profile f p.1 p.2) X := by
    unfold profile
    apply ContDiffOn.mul
    · apply contDiff_fst.contDiffOn.sqrt
      intro p hp
      have hp1 : 1 ≤ p.1 := hp.1.1
      linarith
    · have hpoly : ContDiff ℝ 1 (fun p : ℝ × ℝ => p.1 * p.2 / 2) := by fun_prop
      exact (hf.comp hpoly).contDiffOn
  have hXcompact : IsCompact X := isCompact_Icc.prod isCompact_Icc
  have hXconvex : Convex ℝ X := (convex_Icc (1 : ℝ) 2).prod (convex_Icc (-A) A)
  obtain ⟨K,hK⟩ := hcd.exists_lipschitzOnWith (by norm_num : (1 : WithTop ℕ∞) ≠ 0)
    hXconvex hXcompact
  obtain ⟨B,hB⟩ := hXcompact.exists_bound_of_continuousOn hcd.continuousOn
  refine ⟨max B 0 + 1, by positivity, (K : ℝ) + 1, by positivity, ?_⟩
  intro r hr1 hr2 t ht
  have hrt : (r,t) ∈ X := ⟨⟨hr1,hr2⟩,ht⟩
  have h1t : ((1 : ℝ),t) ∈ X := ⟨⟨le_rfl,by norm_num⟩,ht⟩
  constructor
  · have hh := hB (r,t) hrt
    simp only [Real.norm_eq_abs] at hh
    exact hh.trans (by linarith [le_max_left B 0])
  · have hh := hK.dist_le_mul (r,t) hrt (1,t) h1t
    simp only [dist_prod_same_right,Real.dist_eq,abs_of_nonneg (sub_nonneg.mpr hr1)] at hh
    exact hh.trans (by nlinarith)

/-- Bounds for both native rank profiles. Constants are actual finite reals. -/
theorem exists_native_profile_bounds {A : ℝ} (hA : 0 < A) :
    ∃ B : ℝ, 0 < B ∧ ∃ K : ℝ, 0 < K ∧
      ∀ r : ℝ, 1 ≤ r → r ≤ 2 → ∀ t ∈ interval A,
        |coshProfile r t| ≤ B ∧ |sinhProfile r t| ≤ B ∧
        |coshProfile r t - coshProfile 1 t| ≤ K * (r - 1) ∧
        |sinhProfile r t - sinhProfile 1 t| ≤ K * (r - 1) := by
  obtain ⟨Bc,hBc,Kc,hKc,hc⟩ := exists_profile_bounds hA Real.contDiff_cosh
  obtain ⟨Bs,hBs,Ks,hKs,hs⟩ := exists_profile_bounds hA Real.contDiff_sinh
  refine ⟨Bc + Bs, by positivity, Kc + Ks, by positivity, ?_⟩
  intro r hr1 hr2 t ht
  have hcr := hc r hr1 hr2 t ht
  have hsr := hs r hr1 hr2 t ht
  dsimp only [coshProfile,sinhProfile]
  refine ⟨hcr.1.trans (by linarith),hsr.1.trans (by linarith),
    hcr.2.trans ?_,hsr.2.trans ?_⟩ <;> nlinarith

end RhDilationRank
#print axioms RhDilationRank.exists_profile_bounds
#print axioms RhDilationRank.exists_native_profile_bounds
