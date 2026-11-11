module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Straightening.StraighteningBaseChangeRestriction
public import SerrePositivity.KST.LocalizingInvariants.LocalizationUniqueness
public import SerrePositivity.KST.Fibration.TransportSectionBaseChangePoint
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftStraighteningBaseChange
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHomEvaluationNaturality

/-! # 同じ straightening 底変換同型を全単体へ戻すと、元の指定比較を回収する -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration
variable {B D : SSet.{u}} (k : D ⟶ B)

/-- Sp の前合成充満忠実性を使い、元の大域同型の制限が同じ指定比較であると回収する。 -/
theorem leftStraighteningSectionJointDiagram_baseChangeIso_pre [Quasicategory D] :
    (hoFunctor.map ((pre ((SSet.uliftFunctor.{u + 1, u}).map
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFirstVertexMap D))).app
        ((ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationInfinity B)).obj _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}))).toFunctor.map
          (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningSectionJointDiagram_baseChangeIso k).hom =
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Straightening.straighteningJointBaseChangeRestrictionIso k).hom := by
  exact (localizationPre_fullyFaithful
    (Y := (ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationInfinity B)).obj _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) _ _
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.transportSimplexFirstVertexMap_ulift_isLocalization.{u, u + 1} D)
    ).toHoFullyFaithful.map_preimage _

/-- 初頂点の同じ値で、元の大域成分を元の全単体上の指定成分として回収する。 -/
theorem leftStraighteningSectionJointDiagram_baseChangeIso_value [Quasicategory D]
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.TransportSimplexCategory D) :
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningSectionJointDiagram_baseChangeIso k).hom
      (ULift.up ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFirstVertexMap D).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex c))) =
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Straightening.straighteningJointBaseChangeRestrictionIso k).hom
      (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex c)) := by
  let l := (SSet.uliftFunctor.{u + 1, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFirstVertexMap D)
  let a := ULift.up.{u + 1} (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex c)
  let F := (SSet.uliftFunctor.{u + 1, u}).map k ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningSectionJointDiagram B
  let G := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningSectionJointDiagram D ≫
    (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftFibrationInfinityBaseChange k)).app _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}
  have h := congrArg (fun m : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (l ≫ F) (l ≫ G) => _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate m a)
    (leftStraighteningSectionJointDiagram_baseChangeIso_pre k)
  have hp := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate_precomp
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningSectionJointDiagram_baseChangeIso k).hom l a
  exact hp.symm.trans h

end SerrePositivity.KST.Fibration
