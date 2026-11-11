module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceSquareLimits
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CatInfinity.StrictNativeConeLeg

/-!
概要：正方形から作った空間の極限錐の元の二射影の回収。
方針：通常の錐の成分を計算して coherent な脚の一単体へ戻す。
規約：元の頂点と pinched 単体の値を保持する。
使われ方：Tamme Remark 6 の写像空間の引き戻し正方形。

対応節は Kerodon 5.5（Tag 01YV）。
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
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC


variable {K E D B : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}} (p : E ⟶ B) (q : D ⟶ B)
variable (a : K.obj ⟶ E.obj) (b : K.obj ⟶ D.obj)
variable (h : IsPullback a b (show E.obj ⟶ B.obj from p) (show D.obj ⟶ B.obj from q))
/-- 概要：空間の極限錐の二射影は元の正方形の指定射に一致する。
方針：strict な錐の成分と辺の公式を適用する。
規約：辺の類でなく一単体を厳密に回収する。
使われ方：対象間写像空間の極限錐と元の射影の照合。 -/
lemma spaceSquareOrdinaryCone_left :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.spaceSquareOrdinaryCone p q a b h).π.app (AsSmall.up.obj WalkingCospan.left) =
      (show K ⟶ E from a) := by
  change a ≫ 𝟙 E.obj = a
  exact Category.comp_id _
/-- 概要：空間の極限錐の二射影は元の正方形の指定射に一致する。
方針：strict な錐の成分と辺の公式を適用する。
規約：辺の類でなく一単体を厳密に回収する。
使われ方：対象間写像空間の極限錐と元の射影の照合。 -/
lemma spaceSquareOrdinaryCone_right :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.spaceSquareOrdinaryCone p q a b h).π.app (AsSmall.up.obj WalkingCospan.right) =
      (show K ⟶ D from b) := by
  change b ≫ 𝟙 D.obj = b
  exact Category.comp_id _
/-- 概要：空間の極限錐の二射影は元の正方形の指定射に一致する。
方針：strict な錐の成分と辺の公式を適用する。
規約：辺の類でなく一単体を厳密に回収する。
使われ方：対象間写像空間の極限錐と元の射影の照合。 -/
lemma spaceSquareCone_left :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.nativeConeLeg (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.spaceSquareCone p q a b h)
      (ULift.up (ComposableArrows.mk₀ (AsSmall.up.obj WalkingCospan.left)))).edge =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (show K ⟶ E from a)).edge := by
  exact (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CatInfinity.nativeConeLeg_strict (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.spaceSquareOrdinaryCone p q a b h) _).trans
    (congrArg (fun f : K ⟶ E ↦ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge f).edge)
      (spaceSquareOrdinaryCone_left p q a b h))
/-- 概要：空間の極限錐の二射影は元の正方形の指定射に一致する。
方針：strict な錐の成分と辺の公式を適用する。
規約：辺の類でなく一単体を厳密に回収する。
使われ方：対象間写像空間の極限錐と元の射影の照合。 -/
lemma spaceSquareCone_right :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.nativeConeLeg (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.spaceSquareCone p q a b h)
      (ULift.up (ComposableArrows.mk₀ (AsSmall.up.obj WalkingCospan.right)))).edge =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (show K ⟶ D from b)).edge := by
  exact (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CatInfinity.nativeConeLeg_strict (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.spaceSquareOrdinaryCone p q a b h) _).trans
    (congrArg (fun f : K ⟶ D ↦ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge f).edge)
      (spaceSquareOrdinaryCone_right p q a b h))

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
