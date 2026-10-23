module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentCospanNativeLegFiberEvaluation

/-!
概要：全 native 三角形の指定比較を、元の実際の小さい二脚との fiber 内の同型へ移す。
方針：三角形の図式側の切断族の指定同型へ、頂点を明示した小さい fiber 評価を後合成する。
規約：元の指定比較の像を使用。使われ方：模型 fiber 比較の二脚と指定 path の同時比較。
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
local notation "fl" => coherentTransformationTotalMap F X C.toLeft
local notation "fr" => coherentTransformationTotalMap F Y C.toRight

/-- 元の native 全錐の左図式辺の始点を、元の小さい左 fiber で評価した射。 -/
def coherentCospanNativeLeftLegFiberMap :=
  pointedTriangleFaceSections Dl (nativePointedConeTriangleLift c s hs el)
    (nativePointedConeTriangleLift_projection c s hs el) 0 ≫
      coherentCospanNativeLeftSourceFiberEvaluation F X Y Z C b

/-- 同じ native 全錐の右図式辺の始点を、元の小さい右 fiber で評価した射。 -/
def coherentCospanNativeRightLegFiberMap :=
  pointedTriangleFaceSections Dr (nativePointedConeTriangleLift c s hs er)
    (nativePointedConeTriangleLift_projection c s hs er) 0 ≫
      coherentCospanNativeRightSourceFiberEvaluation F X Y Z C b

/-- 指定全三角形比較の左の像は、実際の元の第一 fiber 射との同型。 -/
def coherentCospanNativeLeftLegFiberIso :
    FunctorIso (coherentCospanNativeLeftLegFiberMap F X Y Z C b)
      ((SSet.uliftFunctor.{u + 1, u}).map
        (vertexFiberMap pF pX fl (coherentTransformationTotalMap_projection F X C.toLeft) b)) :=
  functorIsoOfEq
    ((coherentCospanNativeLeftFaceSectionsIso F X Y Z C b 0).postcomp
      (coherentCospanNativeLeftSourceFiberEvaluation F X Y Z C b)) rfl
    (coherentTriangleSourceFiberEvaluation_eq F X Z C.toLeft C.fromLeft C.leftTriangle b Dl
      (coherentCospanNativeLeftTriangleDiagram_eq F X Y Z C b)
      (coherentCospanPointedFiberTriangle_left_projection F b X Y Z C))

/-- 右も同じ全錐と元の全三角形の指定比較から、元の実際の第一 fiber 射へ移る。 -/
def coherentCospanNativeRightLegFiberIso :
    FunctorIso (coherentCospanNativeRightLegFiberMap F X Y Z C b)
      ((SSet.uliftFunctor.{u + 1, u}).map
        (vertexFiberMap pF pY fr (coherentTransformationTotalMap_projection F Y C.toRight) b)) :=
  functorIsoOfEq
    ((coherentCospanNativeRightFaceSectionsIso F X Y Z C b 0).postcomp
      (coherentCospanNativeRightSourceFiberEvaluation F X Y Z C b)) rfl
    (coherentTriangleSourceFiberEvaluation_eq F Y Z C.toRight C.fromRight C.rightTriangle b Dr
      (coherentCospanNativeRightTriangleDiagram_eq F X Y Z C b)
      (coherentCospanPointedFiberTriangle_right_projection F b X Y Z C))

end SerrePositivity.InfinityCategories.F2
