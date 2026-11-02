module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentTriangleTargetFiberEvaluation
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentCospanNativeLegFiberEvaluation

/-!
概要：native 錐の左右の辺の切断を、同じ元の最後の Z の fiber へ終点で評価する。
方針：同じ元の全三角形の表示等式と、明示した終点の fiber 評価を左右に適用する。
規約：最後の fiber は左右で共通。使われ方：左右の指定比較の合成と path の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {B : SSet.{u}}
  (F X Y Z : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
  (C : CoherentTransformationCospanCone F X Y Z) (b : B _⦋0⦌)
local notation "c" => coherentCospanConePointwiseCone F X Y Z C b
local notation "Dl" => SSet.yonedaEquiv.symm (nativeConeTriangle c (SSet.yonedaEquiv horn₂₂.ι₀₂))
local notation "Dr" => SSet.yonedaEquiv.symm (nativeConeTriangle c (SSet.yonedaEquiv horn₂₂.ι₁₂))

/-- 左辺の終点を元の同じ最後の小さい fiber へ戻す評価。 -/
def coherentCospanNativeLeftTargetFiberEvaluation :=
  coherentTriangleTargetFiberEvaluation F X Z C.toLeft C.fromLeft C.leftTriangle b Dl
    (coherentCospanNativeLeftTriangleDiagram_eq F X Y Z C b)

/-- 右辺も元の同じ最後の小さい fiber へ終点で評価する。 -/
def coherentCospanNativeRightTargetFiberEvaluation :=
  coherentTriangleTargetFiberEvaluation F Y Z C.toRight C.fromRight C.rightTriangle b Dr
    (coherentCospanNativeRightTriangleDiagram_eq F X Y Z C b)

/-- 左辺の同じ終点への評価は Kan fibration。 -/
lemma coherentCospanNativeLeftTargetFiberEvaluation_fibration :
    Fibration (coherentCospanNativeLeftTargetFiberEvaluation F X Y Z C b) :=
  coherentTriangleTargetFiberEvaluation_fibration F X Z C.toLeft C.fromLeft
    C.leftTriangle b Dl (coherentCospanNativeLeftTriangleDiagram_eq F X Y Z C b)

/-- 右辺でも同じ終点への評価は Kan fibration。 -/
lemma coherentCospanNativeRightTargetFiberEvaluation_fibration :
    Fibration (coherentCospanNativeRightTargetFiberEvaluation F X Y Z C b) :=
  coherentTriangleTargetFiberEvaluation_fibration F Y Z C.toRight C.fromRight
    C.rightTriangle b Dr (coherentCospanNativeRightTriangleDiagram_eq F X Y Z C b)

end SerrePositivity.InfinityCategories.F2
