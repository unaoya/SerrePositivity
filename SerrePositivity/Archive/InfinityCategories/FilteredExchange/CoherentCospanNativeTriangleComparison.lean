module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.NativePointedTriangleLongComparison
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.ContractibleVertexIsoSpan
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentSmallFiberTriangleInitial

/-!
概要：元の左右 pointed 三角形を、共通の全 native 錐の持ち上げと比較する。
方針：両方の元の始点条件を同じ可縮な三角形延長空間の指定比較へ適用する。
規約：元の全二単体と始点を保持。使われ方：fiber 比較の可換性を全 native 錐へ移す。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {B : SSet.{u}}
  (F X Y Z : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
  (C : CoherentTransformationCospanCone F X Y Z) (b : B _⦋0⦌)
local notation "c" => coherentCospanConePointwiseCone F X Y Z C b
local notation "s" => coherentCospanFiberPointedSource F b
local notation "hs" => coherentCospanFiberPointedSource_projection F X Y Z C b
local notation "a" => coherentNativeTriangleFiberParameters F b
local notation "L" => coherentCospanPointedConeLift F X Y Z C b

/-- 元の左全三角形と全錐からの制限の、全始点固定の選択空間内の指定比較。 -/
def coherentCospanNativeLeftTriangleComparison :=
  nativePointedTriangleComparisonIso c s hs (SSet.yonedaEquiv horn₂₂.ι₀₂)
    (coherentSmallFiberPointedTriangle F X Z C.toLeft C.fromLeft C.leftTriangle b)
    (coherentCospanPointedFiberTriangle_left_projection F b X Y Z C)
    (coherentSmallFiberPointedTriangle_initial F X Z C.toLeft C.fromLeft C.leftTriangle b)

/-- 元の右全三角形と同じ全錐からの制限の、全始点固定の指定比較。 -/
def coherentCospanNativeRightTriangleComparison :=
  nativePointedTriangleComparisonIso c s hs (SSet.yonedaEquiv horn₂₂.ι₁₂)
    (coherentSmallFiberPointedTriangle F Y Z C.toRight C.fromRight C.rightTriangle b)
    (coherentCospanPointedFiberTriangle_right_projection F b X Y Z C)
    (coherentSmallFiberPointedTriangle_initial F Y Z C.toRight C.fromRight C.rightTriangle b)

/-- 共通の全 pointed 錐の左右三角形は同じ長辺の全円柱を厳密に共有する。 -/
lemma coherentCospanPointedConeLift_common_long :
    (stdSimplex.δ (1 : Fin 3) ▷ a) ≫ (cospanConeTriangleLeft ▷ a) ≫ L =
      (stdSimplex.δ (1 : Fin 3) ▷ a) ≫ (cospanConeTriangleRight ▷ a) ≫ L := by
  have h := congrArg
    (fun f : (Δ[1] : SSet.{u + 1}) ⟶ join Δ[0] (horn 2 2 : SSet.{u + 1}) => (f ▷ a) ≫ L)
    cospanCone_isPushout.w
  simpa only [comp_whiskerRight, Category.assoc] using h

/-- 元の左三角形の指定比較を、同じ始点固定の長辺 prism 空間へ写す。 -/
def coherentCospanNativeLeftLongComparison :=
  nativePointedTriangleLongComparisonIso c s hs (SSet.yonedaEquiv horn₂₂.ι₀₂)
    (coherentSmallFiberPointedTriangle F X Z C.toLeft C.fromLeft C.leftTriangle b)
    (coherentCospanPointedFiberTriangle_left_projection F b X Y Z C)
    (coherentSmallFiberPointedTriangle_initial F X Z C.toLeft C.fromLeft C.leftTriangle b)

/-- 元の右三角形の指定比較を、同じ始点固定の長辺 prism 空間へ写す。 -/
def coherentCospanNativeRightLongComparison :=
  nativePointedTriangleLongComparisonIso c s hs (SSet.yonedaEquiv horn₂₂.ι₁₂)
    (coherentSmallFiberPointedTriangle F Y Z C.toRight C.fromRight C.rightTriangle b)
    (coherentCospanPointedFiberTriangle_right_projection F b X Y Z C)
    (coherentSmallFiberPointedTriangle_initial F Y Z C.toRight C.fromRight C.rightTriangle b)

end SerrePositivity.InfinityCategories.F2
