import RhClosedSmoothCore001
import Mathlib.Analysis.InnerProductSpace.LinearMap

/-!
Concrete complete arithmetic bilinear form on the actual weighted Hilbert
space, regarded as a REAL Hilbert space. Complex rank moments are retained
as complex scalars with their real inner product; neither imaginary rank
component is discarded. All translations act on genuine spatial L2 classes.
No positivity, inverse, spectral gap or arithmetic cancellation is assumed.
-/
noncomputable section
open Set MeasureTheory Filter FourierTransform
open scoped Topology BigOperators ENNReal
namespace RhNativeCompleteBilinear
open RhAnchored RhWeightedMeasureEmbedding RhWeightedEnergyIdentity

abbrev Bilinear := WeightedSpace →L[ℝ] WeightedSpace →L[ℝ] ℝ

def graphPair : Bilinear := innerSL ℝ

def spatialPair : Bilinear :=
  (innerSL ℝ).bilinearComp physicalEmbedding physicalEmbedding

/-- The native complete Fourier form, polarized in the real Hilbert structure. -/
def archPair : Bilinear := graphPair - spatialPair

/-- Both signed shifts are present before any symmetrization or estimate. -/
def translation (ell : ℝ) : WholeSpace →L[ℝ] WholeSpace :=
  (Lp.compMeasurePreservingₗᵢ ℝ (fun t : ℝ => t + ell)
    (measurePreserving_add_right volume ell)).toContinuousLinearMap

def twoShift (ell : ℝ) : WholeSpace →L[ℝ] WholeSpace :=
  translation ell + translation (-ell)

def rawShiftPair (ell : ℝ) : Bilinear :=
  (innerSL ℝ).bilinearComp physicalEmbedding ((twoShift ell).comp physicalEmbedding)

/-- Exact real polarization of the native diagonal shift form. -/
def shiftPair (ell : ℝ) : Bilinear :=
  (1 / 2 : ℝ) • (rawShiftPair ell + (rawShiftPair ell).flip)

/-- A genuinely complex moment, real-linear in the physical vector. -/
def profileMoment (R : ℝ) (f : ℝ → ℝ)
    (hf : MemLp f 2 (physicalMeasure R)) : WeightedSpace →L[ℝ] ℂ :=
  ((innerSL ℂ (RhTail.physicalFourierVector R f hf)).restrictScalars ℝ).comp
    physicalEmbedding

def profilePair (R : ℝ) (f : ℝ → ℝ)
    (hf : MemLp f 2 (physicalMeasure R)) : Bilinear :=
  (innerSL ℝ).bilinearComp (profileMoment R f hf) (profileMoment R f hf)

lemma cosh_memLp (R : ℝ) :
    MemLp (fun t : ℝ => Real.cosh (t / 2)) 2 (physicalMeasure R) :=
  RhDilationRank.continuous_memLp (by fun_prop)

lemma sinh_memLp (R : ℝ) :
    MemLp (fun t : ℝ => Real.sinh (t / 2)) 2 (physicalMeasure R) :=
  RhDilationRank.continuous_memLp (by fun_prop)

def coshPair (R : ℝ) : Bilinear :=
  profilePair R (fun t => Real.cosh (t / 2)) (cosh_memLp R)

def sinhPair (R : ℝ) : Bilinear :=
  profilePair R (fun t => Real.sinh (t / 2)) (sinh_memLp R)

/-- Full signed finite-horizon bounded perturbation of the complete Fourier
form. The exact physical scalar, BOTH ranks, and EVERY prescribed prime-power
coefficient are retained; no individually positive replacement is introduced. -/
def boundedPart (R C : ℝ) (N : ℕ) : Bilinear :=
  (-C) • spatialPair + (2 : ℝ) • coshPair R - (2 : ℝ) • sinhPair R -
    ∑ n ∈ Finset.Icc 2 N, RhAllPrime.weight n • shiftPair (Real.log (n : ℝ))

def completeForm (R C : ℝ) (N : ℕ) : Bilinear :=
  archPair + boundedPart R C N

lemma graphPair_apply (F G : WeightedSpace) :
    graphPair F G = inner ℝ F G := rfl

lemma spatialPair_apply (F G : WeightedSpace) :
    spatialPair F G = inner ℝ (physicalEmbedding F) (physicalEmbedding G) := rfl

lemma archPair_apply (F G : WeightedSpace) :
    archPair F G = inner ℝ F G - inner ℝ (physicalEmbedding F) (physicalEmbedding G) := rfl

/-- The abstract graph-minus-mass expression is the ACTUAL native energy. -/
theorem archPair_diagonal (F : WeightedSpace) :
    archPair F F = (RhTail.fullFrequencyEnergy (1 / 2) (physicalEmbedding F)).toReal := by
  rw [archPair_apply, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
  linarith [weighted_norm_square F]

theorem archPair_nonnegative (F : WeightedSpace) : 0 ≤ archPair F F := by
  rw [archPair_diagonal]
  exact ENNReal.toReal_nonneg

lemma shiftPair_apply (ell : ℝ) (F G : WeightedSpace) :
    shiftPair ell F G =
      (inner ℝ (physicalEmbedding F) (twoShift ell (physicalEmbedding G)) +
       inner ℝ (physicalEmbedding G) (twoShift ell (physicalEmbedding F))) / 2 := by
  change (1 / 2 : ℝ) *
    (inner ℝ (physicalEmbedding F) (twoShift ell (physicalEmbedding G)) +
     inner ℝ (physicalEmbedding G) (twoShift ell (physicalEmbedding F))) = _
  ring

lemma shiftPair_diagonal (ell : ℝ) (F : WeightedSpace) :
    shiftPair ell F F = inner ℝ (physicalEmbedding F) (twoShift ell (physicalEmbedding F)) := by
  rw [shiftPair_apply]
  ring

lemma profilePair_diagonal (R : ℝ) (f : ℝ → ℝ)
    (hf : MemLp f 2 (physicalMeasure R)) (F : WeightedSpace) :
    profilePair R f hf F F = ‖profileMoment R f hf F‖ ^ 2 :=
  by
    change inner ℝ (profileMoment R f hf F) (profileMoment R f hf F) = _
    exact real_inner_self_eq_norm_sq _

lemma archPair_symmetric (F G : WeightedSpace) : archPair F G = archPair G F := by
  simp only [archPair_apply]
  rw [real_inner_comm G F, real_inner_comm (physicalEmbedding G) (physicalEmbedding F)]

lemma shiftPair_symmetric (ell : ℝ) (F G : WeightedSpace) :
    shiftPair ell F G = shiftPair ell G F := by
  rw [shiftPair_apply, shiftPair_apply]
  ring

lemma profilePair_symmetric (R : ℝ) (f : ℝ → ℝ)
    (hf : MemLp f 2 (physicalMeasure R)) (F G : WeightedSpace) :
    profilePair R f hf F G = profilePair R f hf G F :=
  by
    change inner ℝ (profileMoment R f hf F) (profileMoment R f hf G) =
      inner ℝ (profileMoment R f hf G) (profileMoment R f hf F)
    exact (real_inner_comm _ _).symm

lemma boundedPart_apply (R C : ℝ) (N : ℕ) (F G : WeightedSpace) :
    boundedPart R C N F G =
      -C * spatialPair F G + 2 * coshPair R F G - 2 * sinhPair R F G -
        ∑ n ∈ Finset.Icc 2 N, RhAllPrime.weight n * shiftPair (Real.log (n : ℝ)) F G := by
  simp only [boundedPart, ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply, smul_eq_mul]

/-- Full arithmetic symmetry, retaining all finite cross-covariances. -/
theorem completeForm_symmetric (R C : ℝ) (N : ℕ) (F G : WeightedSpace) :
    completeForm R C N F G = completeForm R C N G F := by
  change archPair F G + boundedPart R C N F G =
    archPair G F + boundedPart R C N G F
  rw [archPair_symmetric F G, boundedPart_apply, boundedPart_apply,
    spatialPair_apply, spatialPair_apply]
  rw [real_inner_comm (physicalEmbedding G) (physicalEmbedding F)]
  simp only [coshPair, sinhPair, profilePair_symmetric, shiftPair_symmetric]

/-- Restriction to the concrete closed smooth-core Hilbert space is a genuine
continuous bilinear map, not an assumed continuous-form target. -/
def coreInclusion (R : ℝ) : RhClosedSmoothCore.CoreSpace R →L[ℝ] WeightedSpace :=
  (supportedSubspace R).subtypeL.comp (RhClosedSmoothCore.smoothCore R).subtypeL

end RhNativeCompleteBilinear
#print axioms RhNativeCompleteBilinear.archPair_diagonal
#print axioms RhNativeCompleteBilinear.archPair_nonnegative
#print axioms RhNativeCompleteBilinear.completeForm_symmetric
