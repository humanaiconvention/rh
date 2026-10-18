import RhPuncturedFunctional001
import RhThreePieceSmoothSplit001
import RhSmoothJetLifts001

/-! PRIVATE endpoint gluing on the actual complete restricted domain.
The interior AND BOTH collar equations are explicit inputs. Finite-point
removal supplies density; no distribution structure theorem, ambient extension
or unproved arithmetic flux vanishing is assumed in the proof. -/
set_option maxHeartbeats 150000
noncomputable section
open Set MeasureTheory Filter
open scoped Topology ContDiff
namespace RhEndpointWeakGluing
open RhWeightedMeasureEmbedding RhFlatSmoothCore RhPuncturedSmoothCore
open RhPuncturedFunctional RhThreePieceSmoothSplit RhSmoothJetLifts

/-- Vanishing is on literal smooth tests and actual AE representatives. -/
def VanishesOnSmooth (S : ℝ) (U : Set ℝ) (T : FlatCoreSpace S →L[ℝ] ℝ) : Prop :=
  ∀ (f : ℝ → ℝ), ContDiff ℝ ∞ f → HasCompactSupport f → tsupport f ⊆ U →
    ∀ X : FlatCoreSpace S,
      (physicalEmbedding (X : WeightedSpace) =ᵐ[volume] fun t => (f t : ℂ)) → T X = 0

/-- All three open-region equations determine the complete functional;
no independent equation at the two cut points is needed. -/
theorem functional_zero_of_three_regions {R S : ℝ} (hR : 0 < R) (hRS : R < S)
    (T : FlatCoreSpace S →L[ℝ] ℝ)
    (hl : VanishesOnSmooth S (Ioo (-S) (-R)) T)
    (hm : VanishesOnSmooth S (Ioo (-R) R) T)
    (hr : VanishesOnSmooth S (Ioo R S) T) : T = 0 := by
  classical
  have hS : 0 < S := hR.trans hRS
  apply functional_zero_of_punctured S ({-R,R} : Finset ℝ) T
  intro X hX
  obtain ⟨f,hf,hc,hs,ha,hAE⟩ := hX
  have hfm : -R ∉ tsupport f := ha (-R) (by simp)
  have hfp : R ∉ tsupport f := ha R (by simp)
  obtain ⟨hfL,hcL,hsL,hfM,hcM,hsM,hfU,hcU,hsU,hSum⟩ :=
    three_piece_split R S hR f hf hc hs hfm hfp
  have hLS : tsupport (leftPiece R f) ⊆ Ioo (-S) S :=
    (leftCut_tsupport_subset (-R) f).trans hs
  have hMS : tsupport (middlePiece R f) ⊆ Ioo (-S) S :=
    (rightCut_tsupport_subset (-R) (leftCut R f)).trans
      ((leftCut_tsupport_subset R f).trans hs)
  have hUS : tsupport (rightPiece R f) ⊆ Ioo (-S) S :=
    (rightCut_tsupport_subset R f).trans hs
  let L : WeightedSpace := smoothLift hS (leftPiece R f) hfL
  let M : WeightedSpace := smoothLift hS (middlePiece R f) hfM
  let U : WeightedSpace := smoothLift hS (rightPiece R f) hfU
  have hL : physicalEmbedding L =ᵐ[volume] fun t => (leftPiece R f t : ℂ) :=
    smoothLift_physical hS (leftPiece R f) hfL hLS
  have hM : physicalEmbedding M =ᵐ[volume] fun t => (middlePiece R f t : ℂ) :=
    smoothLift_physical hS (middlePiece R f) hfM hMS
  have hU : physicalEmbedding U =ᵐ[volume] fun t => (rightPiece R f t : ℂ) :=
    smoothLift_physical hS (rightPiece R f) hfU hUS
  let XL : FlatCoreSpace S := ⟨L,smooth_generator_mem ⟨leftPiece R f,hfL,hcL,hLS,hL⟩⟩
  let XM : FlatCoreSpace S := ⟨M,smooth_generator_mem ⟨middlePiece R f,hfM,hcM,hMS,hM⟩⟩
  let XU : FlatCoreSpace S := ⟨U,smooth_generator_mem ⟨rightPiece R f,hfU,hcU,hUS,hU⟩⟩
  have hTL : T XL = 0 := hl (leftPiece R f) hfL hcL hsL XL hL
  have hTM : T XM = 0 := hm (middlePiece R f) hfM hcM hsM XM hM
  have hTU : T XU = 0 := hr (rightPiece R f) hfU hcU hsU XU hU
  have hdecomp : X = XL + XM + XU := by
    apply Subtype.ext
    apply physicalEmbedding_injective
    change physicalEmbedding (X : WeightedSpace) = physicalEmbedding (L + M + U)
    rw [map_add,map_add]
    apply Lp.ext
    filter_upwards [hAE,hL,hM,hU,
      Lp.coeFn_add (physicalEmbedding L) (physicalEmbedding M),
      Lp.coeFn_add (physicalEmbedding L + physicalEmbedding M) (physicalEmbedding U)]
      with t hXt hLt hMt hUt hadd1 hadd2
    rw [hadd2]
    simp only [Pi.add_apply]
    rw [hadd1]
    simp only [Pi.add_apply]
    rw [hXt,hLt,hMt,hUt]
    simpa only [Complex.ofReal_add] using congrArg Complex.ofReal (hSum t).symm
  rw [hdecomp,map_add,map_add,hTL,hTM,hTU]
  norm_num

/-- The WHOLE native complete row, with all fixed-cap companions, is zero
once its actual interior and both open-collar equations are known. -/
theorem native_row_zero_of_three_regions {R S : ℝ} (hR : 0 < R) (hRS : R < S)
    (C : ℝ) (N : ℕ) (p : WeightedSpace)
    (hl : VanishesOnSmooth S (Ioo (-S) (-R)) (nativeRow S C N p))
    (hm : VanishesOnSmooth S (Ioo (-R) R) (nativeRow S C N p))
    (hr : VanishesOnSmooth S (Ioo R S) (nativeRow S C N p)) :
    ∀ X : FlatCoreSpace S,
      RhNativeCompleteBilinear.completeForm S C N p (X : WeightedSpace) = 0 := by
  have hz := functional_zero_of_three_regions hR hRS (nativeRow S C N p) hl hm hr
  intro X
  change nativeRow S C N p X = 0
  rw [hz]
  rfl

end RhEndpointWeakGluing
#print axioms RhEndpointWeakGluing.functional_zero_of_three_regions
#print axioms RhEndpointWeakGluing.native_row_zero_of_three_regions