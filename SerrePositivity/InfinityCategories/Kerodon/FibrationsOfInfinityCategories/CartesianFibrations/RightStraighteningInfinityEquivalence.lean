module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.RightFibrationOppositeComparison
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftStraighteningInfinityEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PresheafUnstraightening
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.RightFibrationMappingSpaces

/-!
概要：元の相対 Hom を持つ right fibrations の ∞ 圏は、元の前層 ∞ 圏と同値。
方針：全 Hom の共通解像による反転比較に、反対の底上の同じ空間値 straightening を合成する。
規約：順方向は構成した同じ写像に固定する。対象ごとの存在だけで分類を代用しない。
使われ方：F1-2 の前層による right fibration 分類と既存の right unstraightening の照合。

対応節は Kerodon 5.1（Tag 01T1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations

/-- 元の right fibrations の ∞ 圏から元の空間値前層 ∞ 圏への分類写像。 -/
def rightStraighteningInfinityMap (B : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.RightFibrationInfinity B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PresheafInfinity B :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.rightFibrationOppositeInfinityMap B ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityMap B.op

/-- 構成した同じ right straightening 写像は、元の全写像空間で充満忠実。 -/
lemma rightStraighteningInfinityMap_isFullyFaithful (B : SSet.{u}) [Quasicategory B] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful (rightStraighteningInfinityMap B) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.rightFibrationOppositeInfinityMap_isQCatEquivalence B).isFullyFaithful.comp
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityMap_isFullyFaithful B.op)

/-- 元の right fibration の ∞ 圏から前層の ∞ 圏への同じ分類写像は同値。 -/
lemma rightStraighteningInfinityMap_isQCatEquivalence (B : SSet.{u}) [Quasicategory B] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (rightStraighteningInfinityMap B) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.rightFibrationOppositeInfinityMap_isQCatEquivalence B).comp
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityMap_isQCatEquivalence B.op)

/-- 元の全相対 Hom を持つ right fibrations と前層の分類同値。 -/
def rightStraighteningInfinityEquivalence (B : SSet.{u}) [Quasicategory B] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.RightFibrationInfinity B) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PresheafInfinity B) :=
  (rightStraighteningInfinityMap_isQCatEquivalence B).choose

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
