module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentCospanNativeLongBase
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.NativePointedTriangleLongBaseChange

/-!
概要：元の左右の長辺比較を同じ始点固定 prism 空間へ移す。
方針：底の等式だけを移送し、元の全円柱と指定比較の値を保持する。
規約：始点族も元の比較も選び直さない。使われ方：共通の全錐を介する可換同型の合成。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
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
local notation "dl" => SSet.yonedaEquiv.symm (nativeConeTriangle c el)
local notation "dr" => SSet.yonedaEquiv.symm (nativeConeTriangle c er)
local notation "bl" => (stdSimplex.δ (1 : Fin 3) ▷ a) ≫ fst Δ[2] a ≫ dl
local notation "br" => (stdSimplex.δ (1 : Fin 3) ▷ a) ≫ fst Δ[2] a ≫ dr
local notation "hl" => triangleLongPrism_initial pointedSpaceProjection
  (fst Δ[2] a ≫ dl) (snd Δ[0] a ≫ s) (nativePointedConeTriangle_initial c s hs el)
local notation "hr" => triangleLongPrism_initial pointedSpaceProjection
  (fst Δ[2] a ≫ dr) (snd Δ[0] a ≫ s) (nativePointedConeTriangle_initial c s hs er)
local notation "common" => coherentCospanNativeLongBase F X Y Z C b
local notation "hc" => coherentCospanNativeLongBase_initial F X Y Z C b

/-- 左の長辺延長空間を同じ共通空間へ表示する同型。実延長は変えない。 -/
def coherentCospanNativeLeftLongBaseIso :
    relativeFunctorExtensionSpace pointedSpaceProjection bl (prismEndpoint 0 a) s hl ≅
      coherentCospanNativeLongExtensionSpace F X Y Z C b :=
  relativeExtensionBaseIso pointedSpaceProjection bl common (prismEndpoint 0 a) s hl hc rfl

/-- 右の長辺も底の共通長辺の等式で同じ延長空間へ移す。 -/
def coherentCospanNativeRightLongBaseIso :
    relativeFunctorExtensionSpace pointedSpaceProjection br (prismEndpoint 0 a) s hr ≅
      coherentCospanNativeLongExtensionSpace F X Y Z C b :=
  relativeExtensionBaseIso pointedSpaceProjection br common (prismEndpoint 0 a) s hr hc
    (coherentCospanNativeLongBase_right F X Y Z C b)

/-- 元の左三角形の指定長辺比較の、共通の始点固定 prism 空間内の指定像。 -/
def coherentCospanNativeLeftCommonLongComparison :=
  nativePointedTriangleLongBaseChangeComparison c s hs el common hc rfl
    (coherentSmallFiberPointedTriangle F X Z C.toLeft C.fromLeft C.leftTriangle b)
    (coherentCospanPointedFiberTriangle_left_projection F b X Y Z C)
    (coherentSmallFiberPointedTriangle_initial F X Z C.toLeft C.fromLeft C.leftTriangle b)

/-- 元の右三角形の指定長辺比較の、同じ共通空間内の指定像。 -/
def coherentCospanNativeRightCommonLongComparison :=
  nativePointedTriangleLongBaseChangeComparison c s hs er common hc
    (coherentCospanNativeLongBase_right F X Y Z C b)
    (coherentSmallFiberPointedTriangle F Y Z C.toRight C.fromRight C.rightTriangle b)
    (coherentCospanPointedFiberTriangle_right_projection F b X Y Z C)
    (coherentSmallFiberPointedTriangle_initial F Y Z C.toRight C.fromRight C.rightTriangle b)

end SerrePositivity.InfinityCategories.F2
