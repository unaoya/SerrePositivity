module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.Equivalence
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.MappingSpacePiZero
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.FunctorWhiskerSimplex
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic

/-!
概要：関手空間の合成の固定辺と前後合成の辺の一致。
方針：恒等辺を定値辺へ戻し全単体の合成公式を適用する。
規約：指定された三角形と同型の値を保持する。
使われ方：引き戻し錐と指定 path の比較を簡約する。

対応節は Kerodon 5.5（Tag 01YV）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC

/-- 概要：関手空間の合成の固定辺と前後合成の辺の一致。
方針：恒等辺を定値辺へ戻し全単体の合成公式を適用する。
規約：元の指定同型と辺の類を保持する。
使われ方：引き戻しの二射影の比較と指定 path の整合。 -/
lemma functorComposition_post_edge {X Y Z : SSet.{u}} {f₀ f₁ : X ⟶ Y}
    (e : SSet.Truncated.Edge (X := (truncation 2).obj ((ihom X).obj Y))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f₀) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f₁)) (g : Y ⟶ Z) :
    ((e.tensor (SSet.Truncated.Edge.id
      (X := (truncation 2).obj ((ihom Y).obj Z)) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex g))).map
        ((truncation 2).map (MonoidalClosed.comp X Y Z))).edge =
      (e.map ((truncation 2).map ((ihom X).map g))).edge := by
  exact (congrArg (fun t ↦ (MonoidalClosed.comp X Y Z).app (Opposite.op ⦋1⦌)
    (e.edge, t)) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_one (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex g)).symm).trans
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.functorPostcomposition_simplex g 1 e.edge)
/-- 概要：関手空間の合成の固定辺と前後合成の辺の一致。
方針：恒等辺を定値辺へ戻し全単体の合成公式を適用する。
規約：元の指定同型と辺の類を保持する。
使われ方：引き戻しの二射影の比較と指定 path の整合。 -/
lemma functorComposition_pre_edge {X Y Z : SSet.{u}} {g₀ g₁ : Y ⟶ Z}
    (d : SSet.Truncated.Edge (X := (truncation 2).obj ((ihom Y).obj Z))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex g₀) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex g₁)) (f : X ⟶ Y) :
    (((SSet.Truncated.Edge.id
      (X := (truncation 2).obj ((ihom X).obj Y)) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f)).tensor d).map
        ((truncation 2).map (MonoidalClosed.comp X Y Z))).edge =
      (d.map ((truncation 2).map ((pre f).app Z))).edge := by
  exact (congrArg (fun t ↦ (MonoidalClosed.comp X Y Z).app (Opposite.op ⦋1⦌)
    (t, d.edge)) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_one (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f)).symm).trans
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.functorPrecomposition_simplex f 1 d.edge)

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
