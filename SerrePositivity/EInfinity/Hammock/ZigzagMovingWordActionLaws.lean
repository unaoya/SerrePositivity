module

public import SerrePositivity.EInfinity.Hammock.ZigzagMovingWordAction
public import SerrePositivity.EInfinity.Hammock.ZigzagMovingDiagramWordChange
public import SerrePositivity.EInfinity.Hammock.ZigzagMovingDiagramExt

/-!
# 動く全図式の元の語の作用の単位・合成・表示変更

概要：元の WordAction の法則を全図式の厳密な等式として回収する。
方針：全対象は元の法則、全縦射は同じ cut の成分で照合する。
規約：固定端点性を仮定しない。
使われ方：元の括弧を持つ refinedDiagram の圧縮。
-/

@[expose] public section
universe u v uD vD
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.Zigzag.MovingDiagram
open CategoryTheory

variable {D : Type uD} [Category.{vD} D] {C : Type u} [Category.{v} C]
  {W : MorphismProperty C} [W.IsMultiplicative] {a b c : Word} {A B : D ⥤ C}

lemma wordAction_id (F : MovingDiagram D C W a A B) : wordAction (𝟙 a) F = F := by
  apply ext
  · intro d
    exact WordAction.obj_id (F.obj d)
  · intro d e f j
    exact MovingHom.app_heq (F.map f) (Word.Hom.cut_id a j)

lemma wordAction_comp (f : a ⟶ b) (g : b ⟶ c) (F : MovingDiagram D C W a A B) :
    wordAction (f ≫ g) F = wordAction g (wordAction f F) := by
  apply ext
  · intro d
    exact WordAction.obj_comp f g (F.obj d)
  · intro d e h j
    exact MovingHom.app_heq (F.map h) (Word.Hom.cut_comp f g j)

lemma wordAction_eqToHom (h : a = b) (F : MovingDiagram D C W a A B) :
    wordAction (eqToHom h) F = changeWord h F := by
  cases h
  exact wordAction_id F

lemma changeWord_heq (h : a = b) (F : MovingDiagram D C W a A B) :
    HEq (changeWord h F) F := by cases h; rfl

lemma changeWord_eq_of_heq (h : a = b) (F : MovingDiagram D C W a A B)
    (G : MovingDiagram D C W b A B) (hFG : HEq F G) : changeWord h F = G :=
  eq_of_heq ((changeWord_heq h F).trans hFG)

end SerrePositivity.EInfinity.Hammock.Zigzag.MovingDiagram
