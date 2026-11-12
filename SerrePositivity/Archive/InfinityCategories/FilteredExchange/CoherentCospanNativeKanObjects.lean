module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentCospanNativeComparisonEquivalence
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanIntervalPullbackNative

/-!
概要：元の native 余極限値の二射と比較を Kan 対象間の実際の射として束ねる。
方針：既存の小宇宙の値の射に同じ Kan 対象の表示を付ける。
規約：台の射は元の比較そのもの。使われ方：元の比較辺による 𝒮 の極限錐の輸送。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2
variable {B : SSet.{u}} [Quasicategory B]
  (F X Y Z : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
  (C : CoherentTransformationCospanCone F X Y Z)

/-- 元の native 左外脚を同じ値の Kan 対象間の射として表示する。 -/
def coherentCospanNativeLeftKanMap :
    spaceInfinityObject (coherentDiagramTotalVertex X) ⟶
      spaceInfinityObject (coherentDiagramTotalVertex Z) :=
  coherentTotalMapNativeValueDown X Z (coherentTransformationTotalMap X Z C.fromLeft)

/-- 元の native 右外脚を同じ値の Kan 対象間の射として表示する。 -/
def coherentCospanNativeRightKanMap :
    spaceInfinityObject (coherentDiagramTotalVertex Y) ⟶
      spaceInfinityObject (coherentDiagramTotalVertex Z) :=
  coherentTotalMapNativeValueDown Y Z (coherentTransformationTotalMap Y Z C.fromRight)

/-- 元の native 比較を元の区間引き戻しの Kan 対象への射として表示する。 -/
def coherentCospanNativeComparisonKanMap :
    spaceInfinityObject (coherentDiagramTotalVertex F) ⟶
      intervalPullbackKanObject (coherentCospanNativeLeftKanMap F X Y Z C)
        (coherentCospanNativeRightKanMap F X Y Z C) :=
  coherentCospanConeNativeComparison F X Y Z C

/-- 束ねた比較の台の射は元の native 比較に厳密に一致する。 -/
lemma coherentCospanNativeComparisonKanMap_forget :
    kanObjectForget.map (coherentCospanNativeComparisonKanMap F X Y Z C) =
      coherentCospanConeNativeComparison F X Y Z C := rfl

end SerrePositivity.InfinityCategories.F2
