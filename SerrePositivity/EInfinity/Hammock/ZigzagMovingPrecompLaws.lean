module

public import SerrePositivity.EInfinity.Hammock.ZigzagMovingDiagramPrecomp
public import SerrePositivity.EInfinity.Hammock.ZigzagColumnSplitDiagram
public import SerrePositivity.EInfinity.Hammock.ZigzagMovingDiagramOfFunctor

/-!
# 動く全図式の切断・連結・表示変更と再添字

概要：元の全図式の前合成は、語の表示変更・部分区間・連結を保持する。
方針：全対象・全縦射の定義を回収し、語の等式の帰納を使う。
規約：元の端点関手も同時に前合成する。
使われ方：prefix・残りの図式と元の全単体作用素。
-/

@[expose] public section
universe u v uD vD uI vI
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.Zigzag.MovingDiagram
open CategoryTheory

variable {D : Type uD} [Category.{vD} D] {I : Type uI} [Category.{vI} I]
  {C : Type u} [Category.{v} C] {W : MorphismProperty C} [W.IsMultiplicative]
  {a b : Word} {A B E : D ⥤ C} (K : I ⥤ D)

lemma changeWord_precomp (h : a = b) (F : MovingDiagram D C W a A B) :
    (changeWord h F).precomp K = changeWord h (F.precomp K) := by cases h; rfl

lemma append_precomp (F : MovingDiagram D C W a A B) (G : MovingDiagram D C W b B E) :
    (F.append G).precomp K = (F.precomp K).append (G.precomp K) := rfl

lemma leftPart_precomp (F : MovingDiagram D C W (Word.append a b) A E) :
    (F.precomp K).leftPart = F.leftPart.precomp K := rfl

lemma rightPart_precomp (F : MovingDiagram D C W (Word.append a b) A E) :
    (F.precomp K).rightPart = F.rightPart.precomp K := rfl

lemma ofFunctor_precomp {X Y : C} (F : D ⥤ Zigzag W a X Y) :
    ofFunctor (K ⋙ F) = (ofFunctor F).precomp K := rfl

namespace ColumnSplit
variable {w : Word} {A B : D ⥤ C} (p : Fin w.length) (F : MovingDiagram D C W w A B)

lemma expanded_precomp : expanded p (F.precomp K) = (expanded p F).precomp K :=
  (changeWord_precomp K (Word.ColumnSplit.whole_eq w p).symm F).symm

lemma before_precomp : HEq (before p (F.precomp K)) ((before p F).precomp K) := by
  dsimp only [before]
  rw [expanded_precomp, leftPart_precomp, leftPart_precomp]

lemma middle_precomp : HEq (middle p (F.precomp K)) ((middle p F).precomp K) := by
  dsimp only [middle]
  rw [expanded_precomp, leftPart_precomp, rightPart_precomp]

lemma after_precomp : HEq (after p (F.precomp K)) ((after p F).precomp K) := by
  dsimp only [after]
  rw [expanded_precomp, rightPart_precomp]

end ColumnSplit
end SerrePositivity.EInfinity.Hammock.Zigzag.MovingDiagram
