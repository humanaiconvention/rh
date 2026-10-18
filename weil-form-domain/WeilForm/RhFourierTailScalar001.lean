import RhFinitePrimitiveEndpoint001
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

noncomputable section
open Set MeasureTheory Filter
open scoped Topology Interval BigOperators
namespace RhTail

def multiplier (x b : ℝ) : ℝ := 2*x/(b*(b^2+x))
def multiplierPrime (x b : ℝ) : ℝ := -2*x*(3*b^2+x)/(b^2*(b^2+x)^2)
def multiplierSecond (x b : ℝ) : ℝ :=
  4*x*(6*b^4+3*b^2*x+x^2)/(b^3*(b^2+x)^3)

lemma multiplier_nonneg {x b : ℝ} (hx : 0 ≤ x) (hb : 0 < b) :
    0 ≤ multiplier x b := by unfold multiplier; positivity

lemma multiplier_hasDerivAt {x b : ℝ} (hx : 0 ≤ x) (hb : 0 < b) :
    HasDerivAt (multiplier x) (multiplierPrime x b) b := by
  have hbx : b^2+x ≠ 0 := ne_of_gt (by positivity : 0 < b^2+x)
  have hd := (hasDerivAt_id b).mul (((hasDerivAt_id b).pow 2).add_const x)
  have h := (hasDerivAt_const b (2*x)).div hd (mul_ne_zero (ne_of_gt hb) hbx)
  convert h using 1
  · rfl
  · unfold multiplierPrime
    simp only [Pi.mul_apply, Pi.pow_apply, id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one]
    field_simp
    <;> ring

lemma multiplierPrime_hasDerivAt {x b : ℝ} (hx : 0 ≤ x) (hb : 0 < b) :
    HasDerivAt (multiplierPrime x) (multiplierSecond x b) b := by
  have hbx : b^2+x ≠ 0 := ne_of_gt (by positivity : 0 < b^2+x)
  have hn := ((((hasDerivAt_id b).pow 2).const_mul 3).add_const x).const_mul (-2*x)
  have hd := ((hasDerivAt_id b).pow 2).mul ((((hasDerivAt_id b).pow 2).add_const x).pow 2)
  have h := hn.div hd (mul_ne_zero (pow_ne_zero 2 (ne_of_gt hb)) (pow_ne_zero 2 hbx))
  convert h using 1
  · rfl
  · unfold multiplierSecond
    simp only [Pi.mul_apply, Pi.pow_apply, id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one]
    field_simp
    <;> ring

lemma multiplier_convex {x : ℝ} (hx : 0 ≤ x) :
    ConvexOn ℝ (Ioi 0) (multiplier x) := by
  apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Ioi 0)
      (f' := multiplierPrime x) (f'' := multiplierSecond x)
  · intro b hb
    exact (multiplier_hasDerivAt hx hb).continuousAt.continuousWithinAt
  · intro b hb
    exact (multiplier_hasDerivAt hx (interior_subset hb)).hasDerivWithinAt
  · intro b hb
    exact (multiplierPrime_hasDerivAt hx (interior_subset hb)).hasDerivWithinAt
  · intro b hb
    have hb' : 0 < b := interior_subset hb
    unfold multiplierSecond
    positivity

lemma log_one_add_lower {z : ℝ} (hz : 0 ≤ z) :
    z/(1+z) ≤ Real.log (1+z) := by
  have hp : 0 < 1+z := by linarith
  have he : z/(1+z)=1-(1+z)⁻¹ := by field_simp; ring
  rw [he]
  exact Real.one_sub_inv_le_log_of_pos hp

def tailBeta : ℝ := 4097/2
def tailDelta : ℝ := 4101/8194
def tailTheta : ℝ := 4101/8

lemma tail_constants :
    tailBeta = RhAnchored.beta 1024 ∧
    tailDelta = 1/2+1/tailBeta ∧
    tailTheta = tailDelta*tailBeta/2 := by
  norm_num [tailBeta, tailDelta, tailTheta, RhAnchored.beta, RhAnchored.archIndex]

lemma log_comparison {x b : ℝ} (hx : 0 ≤ x) (hb : 0 < b) :
    (1/2+1/b)*x/(b^2+x) ≤
      (1/2)*Real.log (1+x/b^2)+x/(b*(b^2+x)) := by
  have hz : 0 ≤ x/b^2 := by positivity
  have h := log_one_add_lower hz
  have he : (x/b^2)/(1+x/b^2)=x/(b^2+x) := by
    have hbx : b^2+x ≠ 0 := ne_of_gt (by positivity : 0 < b^2+x)
    field_simp
  rw [he] at h
  have halg : (1/2+1/b)*x/(b^2+x)=
      (1/2)*(x/(b^2+x))+x/(b*(b^2+x)) := by field_simp
  rw [halg]
  linarith

end RhTail
#print axioms RhTail.multiplier_convex
#print axioms RhTail.log_comparison
#print axioms RhTail.tail_constants
