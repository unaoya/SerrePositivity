module

public import SerrePositivity.InfinityCategories.F1.RightFibrationOppositeComparison
public import SerrePositivity.InfinityCategories.F1.LeftStraighteningInfinityEquivalence
public import SerrePositivity.InfinityCategories.F1.PresheafUnstraightening
public import SerrePositivity.InfinityCategories.F1.RightFibrationMappingSpaces

/-!
概要：元の相対 Hom を持つ right fibrations の ∞ 圏は、元の前層 ∞ 圏と同値。
方針：全 Hom の共通解像による反転比較に、反対の底上の同じ空間値 straightening を合成する。
規約：順方向は構成した同じ写像に固定する。対象ごとの存在だけで分類を代用しない。
使われ方：F1-2 の前層による right fibration 分類と既存の right unstraightening の照合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories

/-- 元の right fibrations の ∞ 圏から元の空間値前層 ∞ 圏への分類写像。 -/
def rightStraighteningInfinityMap (B : SSet.{u}) :
    RightFibrationInfinity B ⟶ PresheafInfinity B :=
  rightFibrationOppositeInfinityMap B ≫ leftStraighteningInfinityMap B.op

/-- 構成した同じ right straightening 写像は、元の全写像空間で充満忠実。 -/
lemma rightStraighteningInfinityMap_isFullyFaithful (B : SSet.{u}) [Quasicategory B] :
    IsFullyFaithful (rightStraighteningInfinityMap B) :=
  (rightFibrationOppositeInfinityMap_isQCatEquivalence B).isFullyFaithful.comp
    (leftStraighteningInfinityMap_isFullyFaithful B.op)

/-- 元の right fibration の ∞ 圏から前層の ∞ 圏への同じ分類写像は同値。 -/
lemma rightStraighteningInfinityMap_isQCatEquivalence (B : SSet.{u}) [Quasicategory B] :
    IsQCatEquivalence (rightStraighteningInfinityMap B) :=
  (rightFibrationOppositeInfinityMap_isQCatEquivalence B).comp
    (leftStraighteningInfinityMap_isQCatEquivalence B.op)

/-- 元の全相対 Hom を持つ right fibrations と前層の分類同値。 -/
def rightStraighteningInfinityEquivalence (B : SSet.{u}) [Quasicategory B] :
    QCatEquivalence (RightFibrationInfinity B) (PresheafInfinity B) :=
  (rightStraighteningInfinityMap_isQCatEquivalence B).choose

end SerrePositivity.InfinityCategories
