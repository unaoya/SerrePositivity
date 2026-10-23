module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentCospanNativeLongBaseIso

/-!
概要：共通の長辺空間へ移した左右の指定比較は、同じ全錐の同じ始点頂点を共有する。
方針：底移送の実頂点保持と長辺制限の値を使い、全錐の円柱の厳密な等式へ戻す。
規約：元の指定比較の端点を保持。使われ方：共通空間内で左右の比較を合成する。
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
/-- 左の指定比較を共通空間へ移した始点頂点。 -/
def coherentCospanNativeLeftCommonLongSource :
    (coherentCospanNativeLongExtensionSpace F X Y Z C b) _⦋0⦌ :=
  nativePointedTriangleLongBaseChangeSource c s hs el
    (coherentCospanNativeLongBase F X Y Z C b)
    (coherentCospanNativeLongBase_initial F X Y Z C b) rfl

/-- 右の指定比較を同じ共通空間へ移した始点頂点。 -/
def coherentCospanNativeRightCommonLongSource :
    (coherentCospanNativeLongExtensionSpace F X Y Z C b) _⦋0⦌ :=
  nativePointedTriangleLongBaseChangeSource c s hs er
    (coherentCospanNativeLongBase F X Y Z C b)
    (coherentCospanNativeLongBase_initial F X Y Z C b)
    (coherentCospanNativeLongBase_right F X Y Z C b)

/-- 共通の全錐の三角形表示は、底の等式移送前も同じ長辺円柱を持つ。 -/
lemma coherentCospanNativeTriangleLift_common_long :
    (stdSimplex.δ (1 : Fin 3) ▷ a) ≫ nativePointedConeTriangleLift c s hs el =
      (stdSimplex.δ (1 : Fin 3) ▷ a) ≫ nativePointedConeTriangleLift c s hs er := by
  have h := coherentCospanPointedConeLift_common_long F X Y Z C b
  simpa only [nativePointedConeTriangleLift, coneTriangleInclusion, Equiv.symm_apply_apply,
    cospanConeTriangleLeft, cospanConeTriangleRight, coherentCospanPointedConeLift,
    Category.assoc] using h

/-- 両指定比較の共通空間内の始点は、同じ実円柱の頂点として厳密に等しい。 -/
lemma coherentCospanNativeCommonLongSource_eq :
    coherentCospanNativeLeftCommonLongSource F X Y Z C b =
      coherentCospanNativeRightCommonLongSource F X Y Z C b := by
  unfold coherentCospanNativeLeftCommonLongSource coherentCospanNativeRightCommonLongSource
  apply Subtype.ext
  apply Subtype.ext
  rw [nativePointedTriangleLongBaseChangeSource_value,
    nativePointedTriangleLongBaseChangeSource_value]
  exact congrArg functorVertex (coherentCospanNativeTriangleLift_common_long F X Y Z C b)

end SerrePositivity.InfinityCategories.F2
