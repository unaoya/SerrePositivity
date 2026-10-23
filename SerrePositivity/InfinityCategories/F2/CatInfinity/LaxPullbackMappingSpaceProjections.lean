module

public import SerrePositivity.InfinityCategories.F2.CatInfinity.LaxPullbackMappingSpaceLimit
public import SerrePositivity.InfinityCategories.F2.CatInfinity.SpaceSquareProjections

/-!
概要：対象間写像空間の native な極限錐の脚の回収。
方針：正方形の二射影の辺の回収定理を特殊化する。
規約：元の頂点と pinched 単体の値を保持する。
使われ方：Tamme Remark 6 の写像空間の引き戻し正方形。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

variable {A B C : SSet.{u}} (p : A ⟶ C) (q : B ⟶ C)
variable (x y : (laxPullback p q) _⦋0⦌)
variable [Quasicategory A] [Quasicategory B] [Quasicategory C]
/-- 概要：対象間写像空間の錐の脚は元の指定射影の coherent 辺。
方針：空間の正方形の strict な脚の計算を適用する。
規約：元の辺の一単体を保持する。
使われ方：Tamme Remark 6 の正方形と native な極限性の接続。 -/
lemma laxPullbackMappingSpaceCone_arrow :
    (nativeConeLeg (laxPullbackMappingSpaceCone p q x y)
      (ULift.up (ComposableArrows.mk₀ (AsSmall.up.obj WalkingCospan.left)))).edge =
    (coherentNerveEdge (show laxPullbackMappingKanObject p q x y ⟶
      laxPullbackArrowMappingKanObject p q x y from
      pinchedHomMap (laxPullbackArrow p q) x y)).edge :=
  spaceSquareCone_left _ _ _ _ _
/-- 概要：対象間写像空間の錐の脚は元の指定射影の coherent 辺。
方針：空間の正方形の strict な脚の計算を適用する。
規約：元の辺の一単体を保持する。
使われ方：Tamme Remark 6 の正方形と native な極限性の接続。 -/
lemma laxPullbackMappingSpaceCone_inputs :
    (nativeConeLeg (laxPullbackMappingSpaceCone p q x y)
      (ULift.up (ComposableArrows.mk₀ (AsSmall.up.obj WalkingCospan.right)))).edge =
    (coherentNerveEdge (show laxPullbackMappingKanObject p q x y ⟶
      laxPullbackInputsMappingKanObject p q x y from
      laxPullbackMappingProjections p q x y)).edge :=
  spaceSquareCone_right _ _ _ _ _

end SerrePositivity.InfinityCategories.F2
