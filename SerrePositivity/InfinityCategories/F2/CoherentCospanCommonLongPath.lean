module

public import SerrePositivity.InfinityCategories.F2.CoherentCospanCommonLongSource

/-!
概要：元の左右三角形の指定比較を、同じ長辺延長空間内で合成する。
方針：共通の全錐の始点頂点の等式を介し、元の二つの指定像を合成する。
規約：元の比較の指定値を保持。使われ方：普遍 prism からの局所比較との照合。
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
local notation "common" => coherentCospanNativeLongBase F X Y Z C b
local notation "hc" => coherentCospanNativeLongBase_initial F X Y Z C b

/-- 元の左三角形の長辺を共通の始点固定空間で表す実頂点。 -/
def coherentCospanNativeLeftOldLongVertex :
    (coherentCospanNativeLongExtensionSpace F X Y Z C b) _⦋0⦌ :=
  nativePointedTriangleLongBaseChangeTarget c s hs el common hc rfl
    (coherentSmallFiberPointedTriangle F X Z C.toLeft C.fromLeft C.leftTriangle b)
    (coherentCospanPointedFiberTriangle_left_projection F b X Y Z C)
    (coherentSmallFiberPointedTriangle_initial F X Z C.toLeft C.fromLeft C.leftTriangle b)

/-- 元の右三角形の長辺を同じ共通空間で表す実頂点。 -/
def coherentCospanNativeRightOldLongVertex :
    (coherentCospanNativeLongExtensionSpace F X Y Z C b) _⦋0⦌ :=
  nativePointedTriangleLongBaseChangeTarget c s hs er common hc
    (coherentCospanNativeLongBase_right F X Y Z C b)
    (coherentSmallFiberPointedTriangle F Y Z C.toRight C.fromRight C.rightTriangle b)
    (coherentCospanPointedFiberTriangle_right_projection F b X Y Z C)
    (coherentSmallFiberPointedTriangle_initial F Y Z C.toRight C.fromRight C.rightTriangle b)

/-- 共通の全錐からの二つの元の指定比較を合成した、元の長辺同士の指定同型。 -/
def coherentCospanNativeCommonLongPathIso :
    VertexIso (coherentCospanNativeLeftOldLongVertex F X Y Z C b)
      (coherentCospanNativeRightOldLongVertex F X Y Z C b) :=
  (coherentCospanNativeLeftCommonLongComparison F X Y Z C b).symm ≪≫
    eqToIso (congrArg SSet.HomotopyCategory.mk
      (coherentCospanNativeCommonLongSource_eq F X Y Z C b)) ≪≫
    coherentCospanNativeRightCommonLongComparison F X Y Z C b

/-- 元の二つの指定比較の合成は、同じ二実頂点間の標準指定比較に等しい。 -/
lemma coherentCospanNativeCommonLongPathIso_eq :
    coherentCospanNativeCommonLongPathIso F X Y Z C b =
      (coherentCospanNativeLongExtensionSpace_contractible F X Y Z C b).vertexIso
        (coherentCospanNativeLeftOldLongVertex F X Y Z C b)
        (coherentCospanNativeRightOldLongVertex F X Y Z C b) := by
  have h := coherentCospanNativeLongExtensionSpace_contractible F X Y Z C b
  have := h.kanComplex
  apply Iso.ext
  have ht := h.isTerminalVertex (coherentCospanNativeRightOldLongVertex F X Y Z C b)
  exact ht.isTerminalHo.hom_ext _ _

end SerrePositivity.InfinityCategories.F2
