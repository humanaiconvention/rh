import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Instances.Real.Lemmas

/-! A local finite-dimensional translate span is globally invariant.
This is a pure real linear-action lemma; actual native form covariance and
compact-support consequences are separate obligations. No arithmetic sign
or positivity assertion is made. -/
noncomputable section
set_option maxHeartbeats 150000
open Set Filter
open scoped Topology
namespace RhLocalTranslationSpan
variable {E : Type*} [AddCommGroup E] [Module ℝ E]

variable (T : ℝ → E →ₗ[ℝ] E)


def localSpan (v : E) (eps : ℝ) : Submodule ℝ E :=
  Submodule.span ℝ ((fun a : ℝ => T a v) '' Set.Ioo (-eps) eps)

/-- A finite-dimensional local orbit span contains the entire orbit. The
positive shift margin is extracted from an actual finite generating subset. -/
theorem orbit_mem_of_finite_local_span (hzero : ∀ x, T 0 x = x)
    (hadd : ∀ a b x, T (a+b) x = T a (T b x)) (v : E) {eps : ℝ} (heps : 0 < eps)
    [FiniteDimensional ℝ (localSpan T v eps)] (t : ℝ) :
    T t v ∈ localSpan T v eps := by
  classical
  let W := localSpan T v eps
  let s := (fun a : ℝ => T a v) '' Set.Ioo (-eps) eps
  letI : FiniteDimensional ℝ (Submodule.span ℝ s) := by
    change FiniteDimensional ℝ (localSpan T v eps)
    infer_instance
  obtain ⟨f,hf,hspan,hlin⟩ := Submodule.exists_fun_fin_finrank_span_eq ℝ s
  choose a ha heq using hf
  have hevent : ∀ᶠ h : ℝ in 𝓝 0, ∀ i, a i + h ∈ Set.Ioo (-eps) eps := by
    have hi (i) : ∀ᶠ h : ℝ in 𝓝 0, a i + h ∈ Set.Ioo (-eps) eps := by
      have hc : Tendsto (fun h : ℝ => a i + h) (𝓝 0) (𝓝 (a i)) := by
        simpa using tendsto_const_nhds.add (tendsto_id : Tendsto (fun h : ℝ => h) (𝓝 0) (𝓝 0))
      exact hc (isOpen_Ioo.mem_nhds (ha i))
    exact Filter.eventually_all.mpr hi
  obtain ⟨delta,hdelta,hd⟩ := Metric.eventually_nhds_iff.mp hevent
  have hlocal (h : ℝ) (hh : |h| < delta) (x : E) (hx : x ∈ W) : T h x ∈ W := by
    have hmem : x ∈ Submodule.span ℝ (Set.range f) := by
      rw [hspan]
      exact hx
    clear hx
    induction hmem using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i,rfl⟩ := hx
      rw [← heq i, ← hadd]
      apply Submodule.subset_span
      refine ⟨a i + h, ?_, ?_⟩
      · exact hd (by simpa only [Real.dist_eq, sub_zero] using hh) i
      · congr 1
        ring
    | zero => simpa using (W.zero_mem)
    | add x y hx hy ihx ihy => simpa only [map_add] using W.add_mem ihx ihy
    | smul c x hx ih => simpa only [map_smul] using W.smul_mem c ih
  have hv : v ∈ W := by
    have hm : T 0 v ∈ W := Submodule.subset_span ⟨0,⟨by linarith,heps⟩,rfl⟩
    simpa only [hzero] using hm
  obtain ⟨n,hn⟩ := exists_nat_gt (max (1 : ℝ) (|t|/delta))
  have hn1 : 1 < (n : ℝ) := (le_max_left _ _).trans_lt hn
  have hn0 : (0 : ℝ) < n := by linarith
  let h := t/(n : ℝ)
  have hh : |h| < delta := by
    dsimp [h]
    rw [abs_div, abs_of_pos hn0]
    apply (div_lt_iff₀ hn0).mpr
    have hratio : |t|/delta < (n : ℝ) := (le_max_right _ _).trans_lt hn
    have := (div_lt_iff₀ hdelta).mp hratio
    nlinarith
  have hiter (k : ℕ) : T ((k : ℝ)*h) v ∈ W := by
    induction k with
    | zero => simpa only [Nat.cast_zero, zero_mul, hzero] using hv
    | succ k ih =>
      have he : ((k+1 : ℕ) : ℝ)*h = h+(k : ℝ)*h := by push_cast; ring
      rw [he,hadd]
      exact hlocal h hh _ ih
  have he : (n : ℝ)*h = t := by dsimp [h]; field_simp
  simpa only [he] using hiter n

/-- Consequently every translate maps the whole local orbit span into itself. -/
theorem invariant_of_finite_local_span (hzero : ∀ x, T 0 x = x)
    (hadd : ∀ a b x, T (a+b) x = T a (T b x)) (v : E) {eps : ℝ} (heps : 0 < eps)
    [FiniteDimensional ℝ (localSpan T v eps)] (t : ℝ) (x : E)
    (hx : x ∈ localSpan T v eps) : T t x ∈ localSpan T v eps := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a,ha,rfl⟩ := hx
    rw [← hadd]
    exact orbit_mem_of_finite_local_span T hzero hadd v heps (t+a)
  | zero => simpa using (localSpan T v eps).zero_mem
  | add x y hx hy ihx ihy => simpa only [map_add] using (localSpan T v eps).add_mem ihx ihy
  | smul c x hx ih => simpa only [map_smul] using (localSpan T v eps).smul_mem c ih

end RhLocalTranslationSpan
#print axioms RhLocalTranslationSpan.orbit_mem_of_finite_local_span
#print axioms RhLocalTranslationSpan.invariant_of_finite_local_span


