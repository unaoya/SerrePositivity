module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentCospanRestrictedPrismBase

/-!
概要：既存の実延長からの頂点と native 比較の実長辺頂点を同じ空間で同定する。
方針：元の全円柱の値を照合し、二段の fiber の頂点の一意性を使う。
規約：全空間への包含後の射の類ではなく、同じ選択空間内の頂点の等式を証明する。
使われ方：既存の局所指定比較と元の native 可換同型の照合。
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

/-- 左右の元の普遍 prism は、同じ共通長辺空間内で同じ実頂点となる。 -/
lemma coherentCospanRestrictedUniversal_eq :
    coherentCospanRestrictedUniversalLeft F X Y Z C b =
      coherentCospanRestrictedUniversalRight F X Y Z C b := by
  unfold coherentCospanRestrictedUniversalLeft coherentCospanRestrictedUniversalRight
  apply Subtype.ext
  apply Subtype.ext
  rw [coherentRestrictedPrismUniversalVertex_value, coherentRestrictedPrismUniversalVertex_value,
    C.diagonal_eq]

/-- 元の左の実延長頂点は native 三角形比較に使った同じ長辺頂点。 -/
lemma coherentCospanRestrictedLongLeft_eq :
    coherentCospanRestrictedLongLeft F X Y Z C b =
      coherentCospanNativeLeftOldLongVertex F X Y Z C b := by
  unfold coherentCospanRestrictedLongLeft coherentCospanNativeLeftOldLongVertex
  apply Subtype.ext
  apply Subtype.ext
  rw [coherentRestrictedPrismLongVertex_value, nativePointedTriangleLongBaseChangeTarget_value]

/-- 元の右の実延長頂点も、同じ共通空間内の元の native 長辺頂点に厳密に等しい。 -/
lemma coherentCospanRestrictedLongRight_eq :
    coherentCospanRestrictedLongRight F X Y Z C b =
      coherentCospanNativeRightOldLongVertex F X Y Z C b := by
  unfold coherentCospanRestrictedLongRight coherentCospanNativeRightOldLongVertex
  apply Subtype.ext
  apply Subtype.ext
  rw [coherentRestrictedPrismLongVertex_value, nativePointedTriangleLongBaseChangeTarget_value]

end SerrePositivity.InfinityCategories.F2
