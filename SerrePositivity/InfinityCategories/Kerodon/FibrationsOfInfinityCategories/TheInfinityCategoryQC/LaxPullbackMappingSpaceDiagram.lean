module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.LaxPullbackMappingKanObjects
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceSquareLimits

/-!
概要：原典の二つの下側の写像空間への cospan。
方針：両端評価と p・q の二射の直積を Kan 対象の射にする。
規約：元の頂点と pinched 単体の値を保持する。
使われ方：Tamme Remark 6 の写像空間の引き戻し正方形。

対応節は Kerodon 5.5（Tag 01YV）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC

variable {A B C : SSet.{u}} (p : A ⟶ C) (q : B ⟶ C)
variable (x y : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullback p q) _⦋0⦌)
/-- 概要：原典の二つの下側の写像空間への cospan。
方針：両端評価と p・q の二射の直積を Kan 対象の射にする。
規約：元の四隅と対象間写像空間を保つ。
使われ方：Tamme Remark 6 のホモトピー引き戻しの公開界面。 -/
def laxPullbackMappingEndpointArrow [Quasicategory C] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.laxPullbackArrowMappingKanObject p q x y ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.laxPullbackBaseMappingKanObject p q x y :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.laxPullbackMappingEndpointMap p q x y
/-- 概要：原典の二つの下側の写像空間への cospan。
方針：両端評価と p・q の二射の直積を Kan 対象の射にする。
規約：元の四隅と対象間写像空間を保つ。
使われ方：Tamme Remark 6 のホモトピー引き戻しの公開界面。 -/
def laxPullbackMappingInputArrow [Quasicategory A] [Quasicategory B] [Quasicategory C] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.laxPullbackInputsMappingKanObject p q x y ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.laxPullbackBaseMappingKanObject p q x y :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap p ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullbackFst p q).app (Opposite.op ⦋0⦌) x)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullbackFst p q).app (Opposite.op ⦋0⦌) y) ⊗ₘ
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap q ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullbackSnd p q).app (Opposite.op ⦋0⦌) x)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullbackSnd p q).app (Opposite.op ⦋0⦌) y)
/-- 概要：原典の二つの下側の写像空間への cospan。
方針：両端評価と p・q の二射の直積を Kan 対象の射にする。
規約：元の四隅と対象間写像空間を保つ。
使われ方：Tamme Remark 6 のホモトピー引き戻しの公開界面。 -/
def laxPullbackMappingSpaceDiagram [Quasicategory A] [Quasicategory B] [Quasicategory C] :
    AsSmall.{u} WalkingCospan ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.kanPullbackDiagram (laxPullbackMappingEndpointArrow p q x y)
    (laxPullbackMappingInputArrow p q x y)

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
