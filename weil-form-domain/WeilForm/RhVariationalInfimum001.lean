import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

/-! Supporting classical variational estimates. These do not estimate a
native arithmetic sign or assert a positive lowest value. -/
noncomputable section
namespace RhVariationalInfimum
variable {V : Type*}

def ground (S : Set V) (f : V → ℝ) : ℝ := sInf (f '' S)

lemma ground_le {S : Set V} {f : V → ℝ} (hb : BddBelow (f '' S))
    {x : V} (hx : x ∈ S) : ground S f ≤ f x :=
  csInf_le hb ⟨x,hx,rfl⟩

/-- Affine pointwise form bounds transfer to honest bounded-below infima. -/
theorem affine_infimum_bounds {S : Set V} (hne : S.Nonempty)
    {f g : V → ℝ} (hb : BddBelow (f '' S))
    {a b c d : ℝ} (ha : 0 < a) (hc : 0 < c)
    (hlo : ∀ x ∈ S, a*f x+b ≤ g x)
    (hhi : ∀ x ∈ S, g x ≤ c*f x+d) :
    BddBelow (g '' S) ∧ a*ground S f+b ≤ ground S g ∧
      ground S g ≤ c*ground S f+d := by
  have hgB : BddBelow (g '' S) := by
    refine ⟨a*ground S f+b, ?_⟩
    rintro y ⟨x,hx,rfl⟩
    have hh := mul_le_mul_of_nonneg_left (ground_le hb hx) ha.le
    have ht := hlo x hx
    linarith
  have hlo' : a*ground S f+b ≤ ground S g := by
    apply le_csInf (hne.image g)
    rintro y ⟨x,hx,rfl⟩
    have hh := mul_le_mul_of_nonneg_left (ground_le hb hx) ha.le
    have ht := hlo x hx
    linarith
  have htest : ∀ x ∈ S, (ground S g-d)/c ≤ f x := by
    intro x hx
    have h := (ground_le hgB hx).trans (hhi x hx)
    apply (div_le_iff₀ hc).mpr
    nlinarith
  have hupper : (ground S g-d)/c ≤ ground S f := by
    apply le_csInf (hne.image f)
    rintro y ⟨x,hx,rfl⟩
    exact htest x hx
  refine ⟨hgB,hlo',?_⟩
  have hm := (div_le_iff₀ hc).mp hupper
  nlinarith

/-- Graph-smallness gives ground-value continuity, not preservation of its sign. -/
theorem graph_perturbation_ground_bound {S : Set V} (hne : S.Nonempty)
    {f g energy : V → ℝ} (hb : BddBelow (f '' S))
    {C eta : ℝ} (he0 : 0 ≤ eta) (he1 : eta < 1)
    (hgraph : ∀ x ∈ S, energy x ≤ f x+C)
    (hpert : ∀ x ∈ S, |g x-f x| ≤ eta*energy x) :
    BddBelow (g '' S) ∧ |ground S g-ground S f| ≤ eta*(|ground S f|+C) := by
  have hlo : ∀ x ∈ S, (1-eta)*f x-eta*C ≤ g x := by
    intro x hx
    have hp := (abs_le.mp (hpert x hx)).1
    have hg := mul_le_mul_of_nonneg_left (hgraph x hx) he0
    nlinarith
  have hhi : ∀ x ∈ S, g x ≤ (1+eta)*f x+eta*C := by
    intro x hx
    have hp := (abs_le.mp (hpert x hx)).2
    have hg := mul_le_mul_of_nonneg_left (hgraph x hx) he0
    nlinarith
  obtain ⟨hgB,hl,hu⟩ := affine_infimum_bounds hne hb
    (a:=1-eta) (b := -eta*C) (c:=1+eta) (d:=eta*C)
    (by linarith) (by linarith)
    (fun x hx => by have hh := hlo x hx; nlinarith) hhi
  refine ⟨hgB,abs_le.mpr ⟨?_,?_⟩⟩
  · have hAbs := le_abs_self (ground S f)
    have hh := mul_le_mul_of_nonneg_left hAbs he0
    nlinarith
  · have hAbs := le_abs_self (ground S f)
    have hh := mul_le_mul_of_nonneg_left hAbs he0
    nlinarith

end RhVariationalInfimum
#print axioms RhVariationalInfimum.affine_infimum_bounds
#print axioms RhVariationalInfimum.graph_perturbation_ground_bound
