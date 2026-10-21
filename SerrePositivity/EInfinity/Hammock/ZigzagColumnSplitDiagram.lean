module

public import SerrePositivity.EInfinity.Hammock.WordColumnSplitVertices
public import SerrePositivity.EInfinity.Hammock.ZigzagMovingDiagramWordChange
public import SerrePositivity.EInfinity.Hammock.ZigzagMovingDiagramPartRecovery

/-!
# 元の任意列の前・中央・後の動く図式と厳密な貼り戻し

概要：元の全図式を任意の一列の前後で切り、全対象・全縦射を保って貼り戻す。
方針：語の厳密な分解に沿って表示し、既存の leftPart/rightPart と append_parts を使う。
規約：両端の関手は任意で、元の縦射を固定しない。空の前後の語を含む。
使われ方：非指定生成矢の列切断を前後の全語へ接続する。
-/

@[expose] public section
universe u v uD vD
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.Zigzag.MovingDiagram.ColumnSplit
open CategoryTheory

variable {D : Type uD} [Category.{vD} D] {C : Type u} [Category.{v} C]
  {W : MorphismProperty C} [W.IsMultiplicative] {w : Word} {A B : D ⥤ C}
  (p : Fin w.length) (F : MovingDiagram D C W w A B)

def expanded := changeWord (Word.ColumnSplit.whole_eq w p).symm F

def before := (expanded p F).leftPart.leftPart

def middle := (expanded p F).leftPart.rightPart

def after := (expanded p F).rightPart

def rebuilt := ((before p F).append (middle p F)).append (after p F)

lemma rebuilt_eq : rebuilt p F = expanded p F := by
  dsimp only [rebuilt, before, middle, after]
  rw [append_parts, append_parts]

def recombine : MovingDiagram D C W w A B :=
  changeWord (Word.ColumnSplit.whole_eq w p) (rebuilt p F)

lemma recombine_eq : recombine p F = F := by
  rw [recombine, rebuilt_eq]
  exact changeWord_roundtrip (Word.ColumnSplit.whole_eq w p).symm F

end SerrePositivity.EInfinity.Hammock.Zigzag.MovingDiagram.ColumnSplit
