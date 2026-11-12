module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGCoherentBarMaurerCartan
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StableHomotopyEquation
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.NormalizedProjection
/-!
概要：D の公開 MC 定理を代入し、元の coherent 図式の実 bar と正規化比較を無条件にする。
方針：MC 仮定付き構成を保持し、公開された元の theta の等式をそのまま渡す。
規約：追加の模型圏 instance や別の theta を導入しない。
使われ方：変形 retract と native 余錐の無条件な主経路。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar
open CategoryTheory Limits DifferentialGraded SSet
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (F : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (RightModule R D))

lemma dgCoherentBarMaurerCartan_unconditional : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarMaurerCartan R D F :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarTheta_maurerCartan R D F

abbrev dgCoherentBarModuleUnconditional : RightModule R D :=
  _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarModule R D F (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarTheta_maurerCartan R D F)

abbrev dgCoherentBarNormalizedModuleUnconditional : RightModule R D :=
  _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedModule R D F (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarTheta_maurerCartan R D F)

abbrev dgCoherentBarNormalizedModuleProjectionUnconditional :
    ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) (dgCoherentBarModuleUnconditional R D F) ⟶
      ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) (dgCoherentBarNormalizedModuleUnconditional R D F) :=
  _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedModuleProjection R D F (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarTheta_maurerCartan R D F)

abbrev dgCoherentBarNormalizationEndomorphismUnconditional :
    ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) (dgCoherentBarModuleUnconditional R D F) ⟶
      ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) (dgCoherentBarModuleUnconditional R D F) :=
  _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizationEndomorphism R D F (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarTheta_maurerCartan R D F)

abbrev dgCoherentBarNormalizationEndomorphismHomotopyUnconditional :
    _root_.SerrePositivity.DifferentialGraded.ModuleHomotopy R D (dgCoherentBarNormalizationEndomorphismUnconditional R D F) (𝟙 _) :=
  _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizationEndomorphismHomotopy R D F
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarTheta_maurerCartan R D F)

lemma dgCoherentBarNormalizationProjectorGraded_twisted_closed_unconditional :
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarTwistedEndDifferential R D F 0
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizationProjectorGraded R D F) = 0 :=
  _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizationProjectorGraded_twisted_closed R D F
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarTheta_maurerCartan R D F)

lemma dgCoherentBarNormalizationStableHomotopyGraded_twisted_d_unconditional :
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarTwistedEndDifferential R D F (-1)
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizationStableHomotopyGraded R D F) =
      _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizationProjectorGraded R D F -
      (_root_.SerrePositivity.DifferentialGraded.unitElement R
        (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F))).val :=
  _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizationStableHomotopyGraded_twisted_d R D F
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarTheta_maurerCartan R D F)

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar
