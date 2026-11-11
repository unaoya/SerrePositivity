module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.StageCoefficientComparison
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Unconditional
/-!
概要：正規化した実 coherent bar と元の bar の無条件の変形 retract を与える。
方針：有限段の普遍係数比較から退化消去を証明し、安定作用素で補正した閉包含を降下する。
規約：同じ正規化加群・同じ閉射影を用い、全 dg 作用に自然な ModuleHomotopy を供給する。
使われ方：正規化模型から元の bar の余錐・普遍性・余極限比較への輸送。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract
open CategoryTheory Limits DifferentialGraded SSet
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (F : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (RightModule R D))

lemma dgCoherentBarProjectorCoefficientComparison :
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.DGCoherentBarProjectorCoefficientComparison R D F :=
  _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarProjectorCoefficientComparison_of_stageCoefficientComparison R D F
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarStageCoefficientComparison R D F)

lemma dgCoherentBarNormalizationKillsDegenerate : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.DGCoherentBarNormalizationKillsDegenerate R D F :=
  _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarNormalizationKillsDegenerate_of_projectorCoefficientComparison R D F
    (dgCoherentBarProjectorCoefficientComparison R D F)

def dgCoherentBarNormalizedModuleInclusion (hMC : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarMaurerCartan R D F) :
    ForgetEnrichment.of (Complex R) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedModule R D F hMC) ⟶
      _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarObject R D F hMC :=
  _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarNormalizedModuleInclusionOfDegenerateVanish R D F hMC
    (dgCoherentBarNormalizationKillsDegenerate R D F)

lemma dgCoherentBarNormalizedModuleInclusion_projection (hMC : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarMaurerCartan R D F) :
    dgCoherentBarNormalizedModuleInclusion R D F hMC ≫
      _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedModuleProjection R D F hMC = 𝟙 _ :=
  _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarNormalizedModuleInclusionOfDegenerateVanish_projection R D F hMC
    (dgCoherentBarNormalizationKillsDegenerate R D F)

lemma dgCoherentBarNormalizedModuleProjection_inclusion (hMC : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarMaurerCartan R D F) :
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedModuleProjection R D F hMC ≫
      dgCoherentBarNormalizedModuleInclusion R D F hMC =
      _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizationEndomorphism R D F hMC :=
  _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarNormalizedModuleProjection_inclusionOfDegenerateVanish R D F hMC
    (dgCoherentBarNormalizationKillsDegenerate R D F)

def dgCoherentBarNormalizedModuleRetractHomotopy (hMC : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarMaurerCartan R D F) :
    _root_.SerrePositivity.DifferentialGraded.ModuleHomotopy R D
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedModuleProjection R D F hMC ≫
        dgCoherentBarNormalizedModuleInclusion R D F hMC) (𝟙 _) :=
  _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarNormalizedModuleRetractHomotopyOfDegenerateVanish R D F hMC
    (dgCoherentBarNormalizationKillsDegenerate R D F)

abbrev dgCoherentBarNormalizedModuleInclusionUnconditional :
    ForgetEnrichment.of (Complex R) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedModuleUnconditional R D F) ⟶
      ForgetEnrichment.of (Complex R) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarModuleUnconditional R D F) :=
  dgCoherentBarNormalizedModuleInclusion R D F (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarMaurerCartan_unconditional R D F)

lemma dgCoherentBarNormalizedModuleInclusionUnconditional_projection :
    dgCoherentBarNormalizedModuleInclusionUnconditional R D F ≫
      _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedModuleProjectionUnconditional R D F = 𝟙 _ :=
  dgCoherentBarNormalizedModuleInclusion_projection R D F
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarMaurerCartan_unconditional R D F)

lemma dgCoherentBarNormalizedModuleProjectionUnconditional_inclusion :
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedModuleProjectionUnconditional R D F ≫
      dgCoherentBarNormalizedModuleInclusionUnconditional R D F =
      _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizationEndomorphismUnconditional R D F :=
  dgCoherentBarNormalizedModuleProjection_inclusion R D F
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarMaurerCartan_unconditional R D F)

abbrev dgCoherentBarNormalizedModuleRetractHomotopyUnconditional :
    _root_.SerrePositivity.DifferentialGraded.ModuleHomotopy R D
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedModuleProjectionUnconditional R D F ≫
        dgCoherentBarNormalizedModuleInclusionUnconditional R D F) (𝟙 _) :=
  dgCoherentBarNormalizedModuleRetractHomotopy R D F (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarMaurerCartan_unconditional R D F)

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract
