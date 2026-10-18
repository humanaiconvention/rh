import RhSupportedFourierBound001
import Mathlib.Algebra.Order.Floor.Semiring

/-! An exact finite frequency partition. No sampling identity is presumed
and no arithmetic phase or remainder is discarded. -/
noncomputable section
open Set MeasureTheory Filter FourierTransform
open scoped Topology BigOperators
namespace RhFiniteFourierGrid

def width (Omega : ℝ) (M : ℕ) : ℝ := 2 * Omega / M
def left (Omega : ℝ) (M i : ℕ) : ℝ := -Omega + width Omega M * i
def cell (Omega : ℝ) (M i : ℕ) : Set ℝ := Ico (left Omega M i) (left Omega M (i+1))

lemma width_pos {Omega : ℝ} (hO : 0 < Omega) {M : ℕ} (hM : 0 < M) :
    0 < width Omega M := by unfold width; positivity

lemma mem_cell_iff {Omega : ℝ} (hO : 0 < Omega) {M : ℕ} (hM : 0 < M)
    (i : ℕ) (xi : ℝ) :
    xi ∈ cell Omega M i ↔
      (i : ℝ) ≤ (xi+Omega)/width Omega M ∧
      (xi+Omega)/width Omega M < (i : ℝ)+1 := by
  have hw := width_pos hO hM
  simp only [cell, mem_Ico, left, Nat.cast_add, Nat.cast_one]
  rw [le_div_iff₀ hw, div_lt_iff₀ hw]
  constructor <;> rintro ⟨h1,h2⟩ <;> constructor <;> nlinarith

lemma cell_subset_band {Omega : ℝ} (hO : 0 < Omega) {M : ℕ} (hM : 0 < M)
    (i : Fin M) : cell Omega M i ⊆ Ico (-Omega) Omega := by
  intro xi hx
  have hx' := (mem_cell_iff hO hM i xi).mp hx
  have hw := width_pos hO hM
  have hi : (i : ℝ)+1 ≤ M := by exact_mod_cast i.isLt
  have he : width Omega M * M = 2*Omega := by
    unfold width
    exact div_mul_cancel₀ _ (by exact_mod_cast (ne_of_gt hM))
  constructor
  · have hn : (0 : ℝ) ≤ i := by positivity
    have hh : 0 ≤ (xi+Omega)/width Omega M := hn.trans hx'.1
    have hh' : 0 ≤ xi+Omega := by
      simpa only [zero_mul] using (le_div_iff₀ hw).mp hh
    linarith
  · have hh := (div_lt_iff₀ hw).mp (hx'.2.trans_le hi)
    nlinarith

/-- Each interior band frequency lies in exactly one of the M cells.
The omitted upper endpoint is a null set, never a lost interval. -/
theorem unique_cell {Omega : ℝ} (hO : 0 < Omega) {M : ℕ} (hM : 0 < M)
    {xi : ℝ} (hxi : xi ∈ Ico (-Omega) Omega) :
    ∃! i : Fin M, xi ∈ cell Omega M i := by
  have hw := width_pos hO hM
  let q := (xi+Omega)/width Omega M
  have hq : 0 ≤ q := div_nonneg (by linarith [hxi.1]) hw.le
  have he : (M : ℝ)*width Omega M = 2*Omega := by
    unfold width
    field_simp
  have hqM : q < M := by
    apply (div_lt_iff₀ hw).2
    nlinarith [hxi.2]
  have hi : Nat.floor q < M := (Nat.floor_lt hq).2 hqM
  let i : Fin M := ⟨Nat.floor q,hi⟩
  refine ⟨i, ?_, ?_⟩
  · apply (mem_cell_iff hO hM i xi).2
    exact ⟨Nat.floor_le hq, Nat.lt_floor_add_one q⟩
  · intro j hj
    apply Fin.ext
    exact ((Nat.floor_eq_iff hq).2 ((mem_cell_iff hO hM j xi).mp hj)).symm

lemma cell_distance {Omega : ℝ} (hO : 0 < Omega) {M : ℕ} (hM : 0 < M)
    {i : ℕ} {xi : ℝ} (hxi : xi ∈ cell Omega M i) :
    |xi-left Omega M i| ≤ width Omega M := by
  have h1 := hxi.1
  have h2 := hxi.2
  have he : left Omega M (i+1) = left Omega M i + width Omega M := by
    simp only [left, Nat.cast_add, Nat.cast_one]
    ring
  rw [he] at h2
  rw [abs_of_nonneg (sub_nonneg.mpr h1)]
  linarith

def step (Omega : ℝ) (M : ℕ) (g : ℝ → ℂ) (xi : ℝ) : ℂ :=
  ∑ i : Fin M, (cell Omega M i).indicator (fun _ => g (left Omega M i)) xi

lemma step_eq_at_cell {Omega : ℝ} (hO : 0 < Omega) {M : ℕ} (hM : 0 < M)
    {xi : ℝ} (hxi : xi ∈ Ico (-Omega) Omega) {i : Fin M}
    (hi : xi ∈ cell Omega M i) : step Omega M g xi = g (left Omega M i) := by
  classical
  obtain ⟨j, hj, hu⟩ := unique_cell hO hM hxi
  have hji := hu i hi
  unfold step
  rw [Finset.sum_eq_single i]
  · exact indicator_of_mem hi _
  · intro b _ hbi
    apply indicator_of_notMem
    intro hb
    exact hbi ((hu b hb).trans hji.symm)
  · intro hn
    exact (hn (Finset.mem_univ i)).elim

lemma step_zero_outside {Omega : ℝ} (hO : 0 < Omega) {M : ℕ} (hM : 0 < M)
    {xi : ℝ} (hxi : xi ∉ Ico (-Omega) Omega) : step Omega M g xi = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  exact indicator_of_notMem (fun h => hxi (cell_subset_band hO hM i h)) _

end RhFiniteFourierGrid
#print axioms RhFiniteFourierGrid.unique_cell
#print axioms RhFiniteFourierGrid.cell_distance
#print axioms RhFiniteFourierGrid.step_eq_at_cell
#print axioms RhFiniteFourierGrid.step_zero_outside
