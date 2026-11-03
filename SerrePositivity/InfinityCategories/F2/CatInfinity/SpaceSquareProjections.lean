module

public import SerrePositivity.InfinityCategories.F2.CatInfinity.SpaceSquareLimits
public import SerrePositivity.InfinityCategories.HomotopyLimits.CatInfinity.StrictNativeConeLeg

/-!
概要：正方形から作った空間の極限錐の元の二射影の回収。
方針：通常の錐の成分を計算して coherent な脚の一単体へ戻す。
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

open HomotopyLimits
variable {K E D B : KanObject.{u}} (p : E ⟶ B) (q : D ⟶ B)
variable (a : K.obj ⟶ E.obj) (b : K.obj ⟶ D.obj)
variable (h : IsPullback a b (show E.obj ⟶ B.obj from p) (show D.obj ⟶ B.obj from q))
/-- 概要：空間の極限錐の二射影は元の正方形の指定射に一致する。
方針：strict な錐の成分と辺の公式を適用する。
規約：辺の類でなく一単体を厳密に回収する。
使われ方：対象間写像空間の極限錐と元の射影の照合。 -/
lemma spaceSquareOrdinaryCone_left :
    (spaceSquareOrdinaryCone p q a b h).π.app (AsSmall.up.obj WalkingCospan.left) =
      (show K ⟶ E from a) := by
  change a ≫ 𝟙 E.obj = a
  exact Category.comp_id _
/-- 概要：空間の極限錐の二射影は元の正方形の指定射に一致する。
方針：strict な錐の成分と辺の公式を適用する。
規約：辺の類でなく一単体を厳密に回収する。
使われ方：対象間写像空間の極限錐と元の射影の照合。 -/
lemma spaceSquareOrdinaryCone_right :
    (spaceSquareOrdinaryCone p q a b h).π.app (AsSmall.up.obj WalkingCospan.right) =
      (show K ⟶ D from b) := by
  change b ≫ 𝟙 D.obj = b
  exact Category.comp_id _
/-- 概要：空間の極限錐の二射影は元の正方形の指定射に一致する。
方針：strict な錐の成分と辺の公式を適用する。
規約：辺の類でなく一単体を厳密に回収する。
使われ方：対象間写像空間の極限錐と元の射影の照合。 -/
lemma spaceSquareCone_left :
    (nativeConeLeg (spaceSquareCone p q a b h)
      (ULift.up (ComposableArrows.mk₀ (AsSmall.up.obj WalkingCospan.left)))).edge =
      (coherentNerveEdge (show K ⟶ E from a)).edge := by
  exact (nativeConeLeg_strict (spaceSquareOrdinaryCone p q a b h) _).trans
    (congrArg (fun f : K ⟶ E ↦ (coherentNerveEdge f).edge)
      (spaceSquareOrdinaryCone_left p q a b h))
/-- 概要：空間の極限錐の二射影は元の正方形の指定射に一致する。
方針：strict な錐の成分と辺の公式を適用する。
規約：辺の類でなく一単体を厳密に回収する。
使われ方：対象間写像空間の極限錐と元の射影の照合。 -/
lemma spaceSquareCone_right :
    (nativeConeLeg (spaceSquareCone p q a b h)
      (ULift.up (ComposableArrows.mk₀ (AsSmall.up.obj WalkingCospan.right)))).edge =
      (coherentNerveEdge (show K ⟶ D from b)).edge := by
  exact (nativeConeLeg_strict (spaceSquareOrdinaryCone p q a b h) _).trans
    (congrArg (fun f : K ⟶ D ↦ (coherentNerveEdge f).edge)
      (spaceSquareOrdinaryCone_right p q a b h))

end SerrePositivity.InfinityCategories.F2
