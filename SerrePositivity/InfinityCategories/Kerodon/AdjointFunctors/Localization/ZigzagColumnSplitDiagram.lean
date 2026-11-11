module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordColumnSplitVertices
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingDiagramWordChange
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingDiagramPartRecovery

/-!
# 元の任意列の前・中央・後の動く図式と厳密な貼り戻し

概要：元の全図式を任意の一列の前後で切り、全対象・全縦射を保って貼り戻す。
方針：語の厳密な分解に沿って表示し、既存の leftPart/rightPart と append_parts を使う。
規約：両端の関手は任意で、元の縦射を固定しない。空の前後の語を含む。
使われ方：非指定生成矢の列切断を前後の全語へ接続する。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v uD vD
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagColumnSplitDiagram
open CategoryTheory

variable {D : Type uD} [Category.{vD} D] {C : Type u} [Category.{v} C]
  {W : MorphismProperty C} [W.IsMultiplicative] {w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} {A B : D ⥤ C}
  (p : Fin w.length) (F : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingDiagram D C W w A B)

def expanded := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.changeWord (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordColumnSplit.whole_eq w p).symm F

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingDiagram.ColumnSplit.expanded export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagColumnSplitDiagram (expanded)


def before := (expanded p F).leftPart.leftPart

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingDiagram.ColumnSplit.before export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagColumnSplitDiagram (before)


def middle := (expanded p F).leftPart.rightPart

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingDiagram.ColumnSplit.middle export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagColumnSplitDiagram (middle)


def after := (expanded p F).rightPart

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingDiagram.ColumnSplit.after export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagColumnSplitDiagram (after)


def rebuilt := ((before p F).append (middle p F)).append (after p F)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingDiagram.ColumnSplit.rebuilt export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagColumnSplitDiagram (rebuilt)


lemma rebuilt_eq : rebuilt p F = expanded p F := by
  dsimp only [rebuilt, before, middle, after]
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.append_parts, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.append_parts]

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingDiagram.ColumnSplit.rebuilt_eq export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagColumnSplitDiagram (rebuilt_eq)


def recombine : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingDiagram D C W w A B :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.changeWord (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordColumnSplit.whole_eq w p) (rebuilt p F)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingDiagram.ColumnSplit.recombine export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagColumnSplitDiagram (recombine)


lemma recombine_eq : recombine p F = F := by
  rw [recombine, rebuilt_eq]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.changeWord_roundtrip (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordColumnSplit.whole_eq w p).symm F

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingDiagram.ColumnSplit.recombine_eq export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagColumnSplitDiagram (recombine_eq)


end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagColumnSplitDiagram
