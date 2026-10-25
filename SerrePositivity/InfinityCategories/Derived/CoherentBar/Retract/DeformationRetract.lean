module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.Retract.StageCoefficientComparison
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.Unconditional
/-!
概要：正規化した実 coherent bar と元の bar の無条件の変形 retract を与える。
方針：有限段の普遍係数比較から退化消去を証明し、安定作用素で補正した閉包含を降下する。
規約：同じ正規化加群・同じ閉射影を用い、全 dg 作用に自然な ModuleHomotopy を供給する。
使われ方：正規化模型から元の bar の余錐・普遍性・余極限比較への輸送。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve SSet
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (F : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ dgNerve R (RightModule R D))

lemma dgCoherentBarProjectorCoefficientComparison :
    DGCoherentBarProjectorCoefficientComparison R D F :=
  dgCoherentBarProjectorCoefficientComparison_of_stageCoefficientComparison R D F
    (dgCoherentBarStageCoefficientComparison R D F)

lemma dgCoherentBarNormalizationKillsDegenerate : DGCoherentBarNormalizationKillsDegenerate R D F :=
  dgCoherentBarNormalizationKillsDegenerate_of_projectorCoefficientComparison R D F
    (dgCoherentBarProjectorCoefficientComparison R D F)

def dgCoherentBarNormalizedModuleInclusion (hMC : dgCoherentBarMaurerCartan R D F) :
    ForgetEnrichment.of (Complex R) (dgCoherentBarNormalizedModule R D F hMC) ⟶
      dgCoherentBarObject R D F hMC :=
  dgCoherentBarNormalizedModuleInclusionOfDegenerateVanish R D F hMC
    (dgCoherentBarNormalizationKillsDegenerate R D F)

lemma dgCoherentBarNormalizedModuleInclusion_projection (hMC : dgCoherentBarMaurerCartan R D F) :
    dgCoherentBarNormalizedModuleInclusion R D F hMC ≫
      dgCoherentBarNormalizedModuleProjection R D F hMC = 𝟙 _ :=
  dgCoherentBarNormalizedModuleInclusionOfDegenerateVanish_projection R D F hMC
    (dgCoherentBarNormalizationKillsDegenerate R D F)

lemma dgCoherentBarNormalizedModuleProjection_inclusion (hMC : dgCoherentBarMaurerCartan R D F) :
    dgCoherentBarNormalizedModuleProjection R D F hMC ≫
      dgCoherentBarNormalizedModuleInclusion R D F hMC =
      dgCoherentBarNormalizationEndomorphism R D F hMC :=
  dgCoherentBarNormalizedModuleProjection_inclusionOfDegenerateVanish R D F hMC
    (dgCoherentBarNormalizationKillsDegenerate R D F)

def dgCoherentBarNormalizedModuleRetractHomotopy (hMC : dgCoherentBarMaurerCartan R D F) :
    ModuleHomotopy R D
      (dgCoherentBarNormalizedModuleProjection R D F hMC ≫
        dgCoherentBarNormalizedModuleInclusion R D F hMC) (𝟙 _) :=
  dgCoherentBarNormalizedModuleRetractHomotopyOfDegenerateVanish R D F hMC
    (dgCoherentBarNormalizationKillsDegenerate R D F)

abbrev dgCoherentBarNormalizedModuleInclusionUnconditional :
    ForgetEnrichment.of (Complex R) (dgCoherentBarNormalizedModuleUnconditional R D F) ⟶
      ForgetEnrichment.of (Complex R) (dgCoherentBarModuleUnconditional R D F) :=
  dgCoherentBarNormalizedModuleInclusion R D F (dgCoherentBarMaurerCartan_unconditional R D F)

lemma dgCoherentBarNormalizedModuleInclusionUnconditional_projection :
    dgCoherentBarNormalizedModuleInclusionUnconditional R D F ≫
      dgCoherentBarNormalizedModuleProjectionUnconditional R D F = 𝟙 _ :=
  dgCoherentBarNormalizedModuleInclusion_projection R D F
    (dgCoherentBarMaurerCartan_unconditional R D F)

lemma dgCoherentBarNormalizedModuleProjectionUnconditional_inclusion :
    dgCoherentBarNormalizedModuleProjectionUnconditional R D F ≫
      dgCoherentBarNormalizedModuleInclusionUnconditional R D F =
      dgCoherentBarNormalizationEndomorphismUnconditional R D F :=
  dgCoherentBarNormalizedModuleProjection_inclusion R D F
    (dgCoherentBarMaurerCartan_unconditional R D F)

abbrev dgCoherentBarNormalizedModuleRetractHomotopyUnconditional :
    ModuleHomotopy R D
      (dgCoherentBarNormalizedModuleProjectionUnconditional R D F ≫
        dgCoherentBarNormalizedModuleInclusionUnconditional R D F) (𝟙 _) :=
  dgCoherentBarNormalizedModuleRetractHomotopy R D F (dgCoherentBarMaurerCartan_unconditional R D F)

end SerrePositivity.InfinityCategories
