module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentCospanNativeTargetFiberEvaluation

/-!
概要：左右の全 native 三角形の指定比較を、元の実際の二つの fiber 合成との同型へ写す。
方針：同じ図式側の切断族の指定同型へ、明示した共通の最後の fiber 評価を後合成する。
規約：元の全三角形比較と二作用を保持。使われ方：共通終点で指定比較を合成する。
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

/-- 左 native 三角形の図式辺の終点を、元の最後の小さい fiber で評価した射。 -/
def coherentCospanNativeLeftFinalFiberMap :=
  pointedTriangleFaceSections Dl (nativePointedConeTriangleLift c s hs el)
    (nativePointedConeTriangleLift_projection c s hs el) 0 ≫
      coherentCospanNativeLeftTargetFiberEvaluation F X Y Z C b

/-- 同じ全錐の右三角形を、同じ最後の小さい fiber で評価した射。 -/
def coherentCospanNativeRightFinalFiberMap :=
  pointedTriangleFaceSections Dr (nativePointedConeTriangleLift c s hs er)
    (nativePointedConeTriangleLift_projection c s hs er) 0 ≫
      coherentCospanNativeRightTargetFiberEvaluation F X Y Z C b

/-- 左の指定比較は、元の実際の二つの fiber 射の合成との同型。 -/
def coherentCospanNativeLeftFinalFiberIso :
    FunctorIso (coherentCospanNativeLeftFinalFiberMap F X Y Z C b)
      ((SSet.uliftFunctor.{u + 1, u}).map (fl ≫ ql)) :=
  functorIsoOfEq
    ((coherentCospanNativeLeftFaceSectionsIso F X Y Z C b 0).postcomp
      (coherentCospanNativeLeftTargetFiberEvaluation F X Y Z C b)) rfl
    (coherentTriangleTargetFiberEvaluation_eq F X Z C.toLeft C.fromLeft C.leftTriangle b Dl
      (coherentCospanNativeLeftTriangleDiagram_eq F X Y Z C b)
      (coherentCospanPointedFiberTriangle_left_projection F b X Y Z C))

/-- 右も同じ全錐の指定比較から、元の実際の二つの fiber 射の合成へ写す。 -/
def coherentCospanNativeRightFinalFiberIso :
    FunctorIso (coherentCospanNativeRightFinalFiberMap F X Y Z C b)
      ((SSet.uliftFunctor.{u + 1, u}).map (fr ≫ qr)) :=
  functorIsoOfEq
    ((coherentCospanNativeRightFaceSectionsIso F X Y Z C b 0).postcomp
      (coherentCospanNativeRightTargetFiberEvaluation F X Y Z C b)) rfl
    (coherentTriangleTargetFiberEvaluation_eq F Y Z C.toRight C.fromRight C.rightTriangle b Dr
      (coherentCospanNativeRightTriangleDiagram_eq F X Y Z C b)
      (coherentCospanPointedFiberTriangle_right_projection F b X Y Z C))

end SerrePositivity.InfinityCategories.F2
