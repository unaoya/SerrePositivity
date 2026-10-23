module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentCospanNativeCommonFiberVertices

/-!
概要：共通長辺の直接 fiber 出力の四つの端点を、元の指定写像の関手頂点へ同定する。
方針：実延長の頂点公式と、元の局所全三角形の最終頂点の厳密な式を使う。
規約：端点の等式を明示。使われ方：native 切断の指定 path と共通長辺の指定像の合成。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {B : SSet.{u}}
  (F X Y Z : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
  (C : CoherentTransformationCospanCone F X Y Z) (b : B _⦋0⦌)
local notation "c" => coherentCospanConePointwiseCone F X Y Z C b
local notation "s" => coherentCospanFiberPointedSource F b
local notation "hs" => coherentCospanFiberPointedSource_projection F X Y Z C b
local notation "el" => SSet.yonedaEquiv horn₂₂.ι₀₂
local notation "er" => SSet.yonedaEquiv horn₂₂.ι₁₂
local notation "Dl" => SSet.yonedaEquiv.symm (nativeConeTriangle c el)
local notation "Dr" => SSet.yonedaEquiv.symm (nativeConeTriangle c er)
local notation "pF" => smallLeftUnstraighteningProjection F
local notation "pX" => smallLeftUnstraighteningProjection X
local notation "pY" => smallLeftUnstraighteningProjection Y
local notation "pZ" => smallLeftUnstraighteningProjection Z
local notation "fl" => vertexFiberMap pF pX (coherentTransformationTotalMap F X C.toLeft)
  (coherentTransformationTotalMap_projection F X C.toLeft) b
local notation "fr" => vertexFiberMap pF pY (coherentTransformationTotalMap F Y C.toRight)
  (coherentTransformationTotalMap_projection F Y C.toRight) b
local notation "ql" => vertexFiberMap pX pZ (coherentTransformationTotalMap X Z C.fromLeft)
  (coherentTransformationTotalMap_projection X Z C.fromLeft) b
local notation "qr" => vertexFiberMap pY pZ (coherentTransformationTotalMap Y Z C.fromRight)
  (coherentTransformationTotalMap_projection Y Z C.fromRight) b
local notation "M" => coherentCospanNativeCommonFiberOutput F X Y Z C b

/-- 共通左始点の像は、同じ native 全錐の左最終 fiber 写像。 -/
lemma coherentCospanNativeCommonFiberOutput_source_left :
    (M).app _ (coherentCospanNativeLeftCommonLongSource F X Y Z C b) =
      functorVertex (coherentCospanNativeLeftFinalFiberMap F X Y Z C b) :=
  coherentCospanNativeCommonFiberOutput_left_vertex F X Y Z C b
    (nativePointedConeTriangleLift c s hs el)
    (nativePointedConeTriangleLift_projection c s hs el)
    (nativePointedConeTriangleLift_initial c s hs el)

/-- 共通右始点も同じ全錐の右最終 fiber 写像へ写る。 -/
lemma coherentCospanNativeCommonFiberOutput_source_right :
    (M).app _ (coherentCospanNativeRightCommonLongSource F X Y Z C b) =
      functorVertex (coherentCospanNativeRightFinalFiberMap F X Y Z C b) :=
  coherentCospanNativeCommonFiberOutput_right_vertex F X Y Z C b
    (nativePointedConeTriangleLift c s hs er)
    (nativePointedConeTriangleLift_projection c s hs er)
    (nativePointedConeTriangleLift_initial c s hs er)

/-- 元の左局所三角形の長辺は、元の実際の二 fiber 射の合成へ写る。 -/
lemma coherentCospanNativeCommonFiberOutput_target_left :
    (M).app _ (coherentCospanNativeLeftOldLongVertex F X Y Z C b) =
      functorVertex ((SSet.uliftFunctor.{u + 1, u}).map (fl ≫ ql)) := by
  have h := coherentCospanNativeCommonFiberOutput_left_vertex F X Y Z C b
    (coherentSmallFiberPointedTriangle F X Z C.toLeft C.fromLeft C.leftTriangle b)
    (coherentCospanPointedFiberTriangle_left_projection F b X Y Z C)
    (coherentSmallFiberPointedTriangle_initial F X Z C.toLeft C.fromLeft C.leftTriangle b)
  exact h.trans (congrArg functorVertex (coherentTriangleTargetFiberEvaluation_eq
    F X Z C.toLeft C.fromLeft C.leftTriangle b Dl
    (coherentCospanNativeLeftTriangleDiagram_eq F X Y Z C b)
    (coherentCospanPointedFiberTriangle_left_projection F b X Y Z C)))

/-- 元の右局所三角形も同じ最後の fiber の実際の二作用へ写る。 -/
lemma coherentCospanNativeCommonFiberOutput_target_right :
    (M).app _ (coherentCospanNativeRightOldLongVertex F X Y Z C b) =
      functorVertex ((SSet.uliftFunctor.{u + 1, u}).map (fr ≫ qr)) := by
  have h := coherentCospanNativeCommonFiberOutput_right_vertex F X Y Z C b
    (coherentSmallFiberPointedTriangle F Y Z C.toRight C.fromRight C.rightTriangle b)
    (coherentCospanPointedFiberTriangle_right_projection F b X Y Z C)
    (coherentSmallFiberPointedTriangle_initial F Y Z C.toRight C.fromRight C.rightTriangle b)
  exact h.trans (congrArg functorVertex (coherentTriangleTargetFiberEvaluation_eq
    F Y Z C.toRight C.fromRight C.rightTriangle b Dr
    (coherentCospanNativeRightTriangleDiagram_eq F X Y Z C b)
    (coherentCospanPointedFiberTriangle_right_projection F b X Y Z C)))

end SerrePositivity.InfinityCategories.F2
