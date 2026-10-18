import RhAnchoredSignedConvolution001
import RhAnchoredCumulativeLedger001
import Mathlib.Analysis.Calculus.Deriv.Abs

noncomputable section
open MeasureTheory Set Filter
open scoped Topology Interval BigOperators
namespace RhAnchored

lemma abs_hasDerivAt_orientation {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (fun y : ℝ => |y|) (orientation x) x := by
  by_cases hneg : x < 0
  · simpa only [orientation, ite_eq_left hneg] using hasDerivAt_abs_neg hneg
  · have hpos : 0 < x := lt_of_le_of_ne (le_of_not_gt hneg) (Ne.symm hx)
    simpa only [orientation, ite_eq_right hneg] using hasDerivAt_abs_pos hpos

lemma hinge_hasDerivAt_slope {L x : ℝ} (hL : 0 < L) (hxP : x ≠ L) (hxM : x ≠ -L) :
    HasDerivAt (fun y => max (|y|-L) 0) (hingeSlope L x) x := by
  by_cases hp : L < x
  · have hs : hingeSlope L x = 1 := by
      simp [hingeSlope, hp.le, show -L ≤ x by linarith]
    rw [hs]
    apply ((hasDerivAt_id x).sub_const L).congr_of_eventuallyEq
    filter_upwards [eventually_gt_nhds hp] with y hy
    simp only [abs_of_pos (show 0 < y by linarith), max_eq_left (sub_nonneg.mpr hy.le), id_eq]
  by_cases hm : x < -L
  · have hs : hingeSlope L x = -1 := by
      simp [hingeSlope, not_le.mpr hm, show ¬L ≤ x by linarith]
    rw [hs]
    apply ((hasDerivAt_id x).neg.sub_const L).congr_of_eventuallyEq
    filter_upwards [eventually_lt_nhds hm] with y hy
    simp only [abs_of_neg (show y < 0 by linarith),
      max_eq_left (show 0 ≤ -y-L by linarith), Pi.neg_apply, id_eq]
  have hp' : x < L := lt_of_le_of_ne (le_of_not_gt hp) hxP
  have hm' : -L < x := lt_of_le_of_ne (le_of_not_gt hm) (Ne.symm hxM)
  have hs : hingeSlope L x = 0 := by simp [hingeSlope, not_le.mpr hp', hm'.le]
  rw [hs]
  apply (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds hm' hp'] with y hy
  have hyL : |y| ≤ L := abs_le.mpr ⟨hy.1.le, hy.2.le⟩
  exact max_eq_right (sub_nonpos.mpr hyL)

lemma hyperbolicPotential_hasDerivAt (x : ℝ) :
    HasDerivAt (fun y => -8*(Real.cosh (y/2)-1)) (-4*Real.sinh (x/2)) x := by
  have h := ((((hasDerivAt_id x).div_const 2).cosh).sub_const 1).const_mul (-8)
  convert h using 1 <;> try rfl
  simp only [id_eq]
  ring

lemma archPotentialTerm_hasDerivAt (k : ℕ) {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (fun y => (1-Real.exp (-(beta k)*|y|))/(4*(archIndex k)^2))
      ((beta k)⁻¹*orientation x*Real.exp (-(beta k)*|x|)) x := by
  have habs := abs_hasDerivAt_orientation hx
  have he := (habs.const_mul (-(beta k))).exp
  have hd := ((hasDerivAt_const x (1 : ℝ)).sub he).div_const (4*(archIndex k)^2)
  convert hd using 1 <;> try rfl
  have ha : archIndex k ≠ 0 := by unfold archIndex; positivity
  unfold beta
  field_simp [ha]
  ring

def finitePotentialSlope (C α L : ℝ) (J : ℕ) (x : ℝ) : ℝ :=
  -4*Real.sinh (x/2)+(C/2)*orientation x
  -(∑ k ∈ Finset.range J, (beta k)⁻¹*orientation x*Real.exp (-(beta k)*|x|))
  +α*hingeSlope L x

theorem finitePotential_hasDerivAt {L x : ℝ} (hL : 0 < L) (hx0 : x ≠ 0)
    (hxP : x ≠ L) (hxM : x ≠ -L) (C α : ℝ) (J : ℕ) :
    HasDerivAt (finitePotential C α L J) (finitePotentialSlope C α L J x) x := by
  have hsum := HasDerivAt.fun_sum (u := Finset.range J)
    (fun k _ => archPotentialTerm_hasDerivAt k hx0)
  have habs := (abs_hasDerivAt_orientation hx0).const_mul (C/2)
  have hhinge := (hinge_hasDerivAt_slope hL hxP hxM).const_mul α
  unfold finitePotential finitePotentialSlope
  exact (((hyperbolicPotential_hasDerivAt x).add habs).sub hsum).add hhinge

theorem finiteKernel_section_hasDerivAt {L t u : ℝ} (hL : 0 < L)
    (hu0 : u ≠ 0) (hut : u ≠ t) (huP : u ≠ L) (huM : u ≠ -L)
    (huTP : u ≠ t+L) (huTM : u ≠ t-L) (C α : ℝ) (J : ℕ) :
    HasDerivAt (fun y => finiteKernel C α L J t y)
      (-finitePotentialSlope C α L J (t-u)+finitePotentialSlope C α L J (-u)) u := by
  have h1 := (finitePotential_hasDerivAt hL
    (show t-u ≠ 0 by intro h; apply hut; linarith)
    (show t-u ≠ L by intro h; apply huTM; linarith)
    (show t-u ≠ -L by intro h; apply huTP; linarith) C α J).comp u
      ((hasDerivAt_const u t).sub (hasDerivAt_id u))
  have h2 := (finitePotential_hasDerivAt hL
    (show -u ≠ 0 by intro h; apply hu0; linarith)
    (show -u ≠ L by intro h; apply huM; linarith)
    (show -u ≠ -L by intro h; apply huP; linarith) C α J).comp u
      ((hasDerivAt_id u).neg)
  have hc1 := hasDerivAt_const u (finitePotential C α L J t)
  have hc0 := hasDerivAt_const u (finitePotential C α L J 0)
  have hd := ((h1.sub hc1).sub h2).add hc0
  unfold finiteKernel anchoredKernel
  convert hd using 1 <;> try rfl
  simp only [id_eq, zero_sub, mul_neg_one, sub_zero, add_zero]
  ring

theorem finiteKernel_section_ae_deriv {L : ℝ} (hL : 0 < L) (C α : ℝ) (J : ℕ) (t : ℝ) :
    ∀ᵐ u ∂volume, deriv (fun y => finiteKernel C α L J t y) u =
      -finitePotentialSlope C α L J (t-u)+finitePotentialSlope C α L J (-u) := by
  filter_upwards [ae_ne_const 0, ae_ne_const t, ae_ne_const L, ae_ne_const (-L),
    ae_ne_const (t+L), ae_ne_const (t-L)] with u hu0 hut huP huM huTP huTM
  exact (finiteKernel_section_hasDerivAt hL hu0 hut huP huM huTP huTM C α J).deriv

end RhAnchored
#print axioms RhAnchored.finitePotential_hasDerivAt
#print axioms RhAnchored.finiteKernel_section_ae_deriv
