import RhWeightedPrimitiveLift001

/-! Actual complex scalar compatibility and paired weighted native energy.
No pointwise splitting of Fourier squared moduli is used. -/
noncomputable section
open Set MeasureTheory Filter FourierTransform
open scoped Topology BigOperators ENNReal
namespace RhComplexWeightedBridge
open RhWeightedMeasureEmbedding RhWeightedEnergyIdentity RhWeightedPrimitiveLift

lemma inclusion_complex_smul (c : ℂ) (F : WeightedSpace) :
    inclusion (c • F) = c • inclusion F := by
  apply Lp.ext
  have hc : (c • F : WeightedSpace) =ᵐ[volume] fun t => c • F t :=
    (Measure.absolutelyContinuous_of_le volume_le_weightedMeasure).ae_eq (Lp.coeFn_smul c F)
  filter_upwards [inclusion_ae (c • F), inclusion_ae F, hc,
    Lp.coeFn_smul c (inclusion F)] with t hleft hright hscalar htarget
  rw [hleft, hscalar, htarget]
  dsimp only [Pi.smul_apply]
  rw [hright]

lemma physicalEmbedding_complex_smul (c : ℂ) (F : WeightedSpace) :
    physicalEmbedding (c • F) = c • physicalEmbedding F := by
  change (Lp.fourierTransformₗᵢ ℝ ℂ).symm (inclusion (c • F)) =
    c • (Lp.fourierTransformₗᵢ ℝ ℂ).symm (inclusion F)
  rw [inclusion_complex_smul, map_smul]

lemma pair_norm_bound (F G : WeightedSpace) :
    ‖F + Complex.I • G‖ ^ 2 ≤ 2 * ‖F‖ ^ 2 + 2 * ‖G‖ ^ 2 := by
  have ht := norm_add_le F (Complex.I • G)
  have hi : ‖Complex.I • G‖ = ‖G‖ := by rw [norm_smul, Complex.norm_I, one_mul]
  rw [hi] at ht
  nlinarith [norm_nonneg F, norm_nonneg G, norm_nonneg (F + Complex.I • G),
    sq_nonneg (‖F‖ - ‖G‖)]

lemma pair_physical (F G : WeightedSpace) :
    physicalEmbedding (F + Complex.I • G) =
      physicalEmbedding F + Complex.I • physicalEmbedding G := by
  rw [map_add, physicalEmbedding_complex_smul]

lemma pair_native_energy_finite (F G : WeightedSpace) :
    RhTail.fullFrequencyEnergy (1 / 2)
      (physicalEmbedding F + Complex.I • physicalEmbedding G) < ⊤ := by
  rw [← pair_physical]
  exact weighted_native_energy_finite _

lemma pair_complete_graph_bound (F G : WeightedSpace) :
    ‖physicalEmbedding F + Complex.I • physicalEmbedding G‖ ^ 2 +
      (RhTail.fullFrequencyEnergy (1 / 2)
        (physicalEmbedding F + Complex.I • physicalEmbedding G)).toReal ≤
      2 * ‖F‖ ^ 2 + 2 * ‖G‖ ^ 2 := by
  rw [← pair_physical, ← weighted_norm_square]
  exact pair_norm_bound F G

end RhComplexWeightedBridge
#print axioms RhComplexWeightedBridge.inclusion_complex_smul
#print axioms RhComplexWeightedBridge.physicalEmbedding_complex_smul
#print axioms RhComplexWeightedBridge.pair_native_energy_finite
#print axioms RhComplexWeightedBridge.pair_complete_graph_bound
