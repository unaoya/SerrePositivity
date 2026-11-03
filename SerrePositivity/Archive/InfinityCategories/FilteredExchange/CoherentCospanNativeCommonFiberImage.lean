module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentCospanNativeCommonFiberOutput
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.NativePointedTriangleLongBaseImage

/-!
概要：左右の最終 fiber 同型を、共通長辺の一つの直接評価による同じ指定像へ表示する。
方針：全出力写像の厳密な一致とホモトピー圏の指定像の合成則を使う。
規約：元の左右の指定比較を保持。使われ方：共通の指定 path の像による両者の合成。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {B : SSet.{u}}
  (F X Y Z : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
  (C : CoherentTransformationCospanCone F X Y Z) (b : B _⦋0⦌)
local notation "a" => coherentNativeTriangleFiberParameters F b
local notation "c" => coherentCospanConePointwiseCone F X Y Z C b
local notation "s" => coherentCospanFiberPointedSource F b
local notation "hs" => coherentCospanFiberPointedSource_projection F X Y Z C b
local notation "el" => SSet.yonedaEquiv horn₂₂.ι₀₂
local notation "er" => SSet.yonedaEquiv horn₂₂.ι₁₂
local notation "Dl" => SSet.yonedaEquiv.symm (nativeConeTriangle c el)
local notation "Dr" => SSet.yonedaEquiv.symm (nativeConeTriangle c er)
local notation "Rl" => triangleLongPrismExtensionRestriction pointedSpaceProjection
  (fst Δ[2] a ≫ Dl) (snd Δ[0] a ≫ s) (nativePointedConeTriangle_initial c s hs el)
local notation "Rr" => triangleLongPrismExtensionRestriction pointedSpaceProjection
  (fst Δ[2] a ≫ Dr) (snd Δ[0] a ≫ s) (nativePointedConeTriangle_initial c s hs er)
local notation "M" => coherentCospanNativeCommonFiberOutput F X Y Z C b

/-- 左の指定最終同型は、元の共通長辺比較の同じ直接 fiber 像。 -/
lemma coherentCospanNativeLeftFinalFiberIso_heq_common_image :
    HEq (coherentCospanNativeLeftFinalFiberIso F X Y Z C b)
      (VertexIso.map (coherentCospanNativeLeftCommonLongComparison F X Y Z C b) M) := by
  have hc := vertexIso_map_heq (coherentCospanNativeLeftTriangleComparison F X Y Z C b)
    (coherentCospanNativeLeftFinalFiberOutput_eq_common F X Y Z C b)
  have hm : VertexIso.map (coherentCospanNativeLeftCommonLongComparison F X Y Z C b) M =
      VertexIso.map (coherentCospanNativeLeftTriangleComparison F X Y Z C b)
        (Rl ≫ (coherentCospanNativeLeftLongBaseIso F X Y Z C b).hom ≫ M) := by
    exact nativePointedTriangleLongBaseChangeComparison_post_map c s hs el
      (coherentCospanNativeLongBase F X Y Z C b)
      (coherentCospanNativeLongBase_initial F X Y Z C b) rfl
      (coherentSmallFiberPointedTriangle F X Z C.toLeft C.fromLeft C.leftTriangle b)
      (coherentCospanPointedFiberTriangle_left_projection F b X Y Z C)
      (coherentSmallFiberPointedTriangle_initial F X Z C.toLeft C.fromLeft C.leftTriangle b) M
  exact (coherentCospanNativeLeftFinalFiberIso_heq_image F X Y Z C b).trans
    (hc.trans (heq_of_eq hm.symm))

/-- 右も同じ共通出力写像を使い、元の指定比較の値を保持する。 -/
lemma coherentCospanNativeRightFinalFiberIso_heq_common_image :
    HEq (coherentCospanNativeRightFinalFiberIso F X Y Z C b)
      (VertexIso.map (coherentCospanNativeRightCommonLongComparison F X Y Z C b) M) := by
  have hc := vertexIso_map_heq (coherentCospanNativeRightTriangleComparison F X Y Z C b)
    (coherentCospanNativeRightFinalFiberOutput_eq_common F X Y Z C b)
  have hm : VertexIso.map (coherentCospanNativeRightCommonLongComparison F X Y Z C b) M =
      VertexIso.map (coherentCospanNativeRightTriangleComparison F X Y Z C b)
        (Rr ≫ (coherentCospanNativeRightLongBaseIso F X Y Z C b).hom ≫ M) := by
    exact nativePointedTriangleLongBaseChangeComparison_post_map c s hs er
      (coherentCospanNativeLongBase F X Y Z C b)
      (coherentCospanNativeLongBase_initial F X Y Z C b)
      (coherentCospanNativeLongBase_right F X Y Z C b)
      (coherentSmallFiberPointedTriangle F Y Z C.toRight C.fromRight C.rightTriangle b)
      (coherentCospanPointedFiberTriangle_right_projection F b X Y Z C)
      (coherentSmallFiberPointedTriangle_initial F Y Z C.toRight C.fromRight
        C.rightTriangle b) M
  exact (coherentCospanNativeRightFinalFiberIso_heq_image F X Y Z C b).trans
    (hc.trans (heq_of_eq hm.symm))

end SerrePositivity.InfinityCategories.F2
