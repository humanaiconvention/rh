import RhAnchoredKernel001

noncomputable section
namespace RhSupportPrimeHinge
open RhAnchored

def primeHinge (alpha L t u : ℝ) : ℝ :=
  anchoredKernel (fun x => alpha*max (|x|-L) 0) t u

lemma at_zero {alpha L : ℝ} (hL : 0<L) : alpha*max (|(0:ℝ)|-L) 0=0 := by
  simp only [abs_zero,zero_sub,max_eq_right (by linarith : -L≤0),mul_zero]

lemma diagonal_zero {alpha L r : ℝ} (hL : 0<L) (hr : L/2<r) (hrL : r≤L) :
    primeHinge alpha L r r=0 := by
  have hr0 : 0<r := by linarith
  unfold primeHinge anchoredKernel
  simp only [sub_self,abs_zero,zero_sub,abs_neg,abs_of_pos hr0,
    max_eq_right (by linarith : -L≤0),max_eq_right (sub_nonpos.mpr hrL)]
  ring

lemma reflected_diagonal_zero {alpha L r : ℝ} (hL : 0<L) (hr : L/2<r) (hrL : r≤L) :
    primeHinge alpha L (-r) (-r)=0 := by
  have hr0 : 0<r := by linarith
  unfold primeHinge anchoredKernel
  simp only [sub_self,abs_zero,zero_sub,abs_neg,abs_of_pos hr0,
    max_eq_right (by linarith : -L≤0),max_eq_right (sub_nonpos.mpr hrL)]
  ring

lemma off_diagonal {alpha L r : ℝ} (hL : 0<L) (hr : L/2<r) (hrL : r≤L) :
    primeHinge alpha L r (-r)=alpha*(2*r-L) := by
  have hr0 : 0<r := by linarith
  have hrr : r- -r=2*r := by ring
  have htwo : 0<2*r-L := by linarith
  unfold primeHinge anchoredKernel
  simp only [hrr,abs_neg,abs_of_pos hr0,abs_of_pos (by linarith : 0<2*r),
    abs_zero,zero_sub,max_eq_right (by linarith : -L≤0),
    max_eq_right (sub_nonpos.mpr hrL),max_eq_left htwo.le]
  ring

lemma reflected_off_diagonal {alpha L r : ℝ} (hL : 0<L) (hr : L/2<r) (hrL : r≤L) :
    primeHinge alpha L (-r) r=alpha*(2*r-L) := by
  have hr0 : 0<r := by linarith
  have hrr : -r-r= -(2*r) := by ring
  have htwo : 0<2*r-L := by linarith
  unfold primeHinge anchoredKernel
  simp only [hrr,abs_neg,abs_of_pos hr0,abs_of_pos (by linarith : 0<2*r),
    abs_zero,zero_sub,max_eq_right (by linarith : -L≤0),
    max_eq_right (sub_nonpos.mpr hrL),max_eq_left htwo.le]
  ring

theorem antisymmetric_pair_energy {alpha L r : ℝ} (hL : 0<L)
    (hr : L/2<r) (hrL : r≤L) :
    primeHinge alpha L r r-primeHinge alpha L r (-r)-
      primeHinge alpha L (-r) r+primeHinge alpha L (-r) (-r)=-2*alpha*(2*r-L) := by
  rw [diagonal_zero hL hr hrL,reflected_diagonal_zero hL hr hrL,
    off_diagonal hL hr hrL,reflected_off_diagonal hL hr hrL]
  ring

theorem antisymmetric_pair_negative {alpha L r : ℝ} (halpha : 0<alpha) (hL : 0<L)
    (hr : L/2<r) (hrL : r≤L) :
    primeHinge alpha L r r-primeHinge alpha L r (-r)-
      primeHinge alpha L (-r) r+primeHinge alpha L (-r) (-r)<0 := by
  rw [antisymmetric_pair_energy hL hr hrL]
  have htwo : 0<2*r-L := by linarith
  nlinarith [mul_pos halpha htwo]

theorem even_pair_positive {alpha L r : ℝ} (halpha : 0<alpha) (hL : 0<L)
    (hr : L/2<r) (hrL : r≤L) :
    0<primeHinge alpha L r r+primeHinge alpha L r (-r)+
      primeHinge alpha L (-r) r+primeHinge alpha L (-r) (-r) := by
  rw [diagonal_zero hL hr hrL,reflected_diagonal_zero hL hr hrL,
    off_diagonal hL hr hrL,reflected_off_diagonal hL hr hrL]
  have htwo : 0<2*r-L := by linarith
  nlinarith [mul_pos halpha htwo]

end RhSupportPrimeHinge
#print axioms RhSupportPrimeHinge.diagonal_zero
#print axioms RhSupportPrimeHinge.off_diagonal
#print axioms RhSupportPrimeHinge.antisymmetric_pair_energy
#print axioms RhSupportPrimeHinge.antisymmetric_pair_negative
#print axioms RhSupportPrimeHinge.even_pair_positive
