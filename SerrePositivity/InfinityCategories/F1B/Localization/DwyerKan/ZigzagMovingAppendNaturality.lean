module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.ZigzagAppendNaturalityArrows
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.ZigzagMovingWordAction
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.ZigzagMovingDiagramAppend
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.ZigzagMovingDiagramExt

/-!
# 動く全図式の連結と元の語の作用の自然性

概要：前後の局所端点も動く図式の連結と、元の語の圧縮を交換する。
方針：元の対象の連結自然性と cut の全縦成分の照合を使う。
規約：接合点の縦射も元の射を保持する。
使われ方：内部三列の圧縮を前後の全語へ拡張する。
-/

@[expose] public section
universe u v uD vD
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.ZigzagAppend.Moving
open CategoryTheory

variable {C : Type u} [Category.{v} C] {W : MorphismProperty C} [W.IsMultiplicative]
  {a b a' b' : Word} {X Y Z X' Y' Z' : C}
  {S : Zigzag W a X Y} {S' : Zigzag W a X' Y'}
  {T : Zigzag W b Y Z} {T' : Zigzag W b Y' Z'}

lemma app_naturality (f : a ⟶ a') (g : b ⟶ b')
    (η : Zigzag.MovingHom S S') (θ : Zigzag.MovingHom T T')
    (hj : HEq (η.app (Fin.last a.length)) (θ.app 0))
    (k : Fin ((Word.append a' b').length + 1)) :
    HEq (app η θ ((Word.appendMap f g).cut k))
      (app (WordAction.movingMap f η) (WordAction.movingMap g θ) k) := by
  have hj' : HEq ((WordAction.movingMap f η).app (Fin.last a'.length))
      ((WordAction.movingMap g θ).app 0) :=
    (Zigzag.MovingHom.app_heq η f.cut_last).trans
      (hj.trans (Zigzag.MovingHom.app_heq θ g.cut_zero).symm)
  by_cases hk : k.val ≤ a'.length
  · let i : Fin (a'.length + 1) := ⟨k.val, by omega⟩
    have hki : Word.leftVertex a' b' i = k := Fin.ext rfl
    rw [← hki]
    exact ((app_index_heq η θ (Word.cut_append_left f g i)).trans
      (app_left_heq η θ (f.cut i))).trans
        (app_left_heq (WordAction.movingMap f η) (WordAction.movingMap g θ) i).symm
  · let i : Fin (b'.length + 1) := ⟨k.val - a'.length, by
      have h : k.val < a'.length + b'.length + 1 := k.isLt
      omega⟩
    have hki : Word.rightVertex a' b' i = k := Fin.ext (by dsimp [i, Word.rightVertex]; omega)
    rw [← hki]
    exact ((app_index_heq η θ (Word.cut_append_right f g i)).trans
      (app_right_heq η θ hj (g.cut i))).trans
        (app_right_heq (WordAction.movingMap f η) (WordAction.movingMap g θ) hj' i).symm

end SerrePositivity.EInfinity.Hammock.ZigzagAppend.Moving
namespace SerrePositivity.EInfinity.Hammock.Zigzag.MovingDiagram
open CategoryTheory

variable {D : Type uD} [Category.{vD} D] {C : Type u} [Category.{v} C]
  {W : MorphismProperty C} [W.IsMultiplicative] {a b a' b' : Word} {A B E : D ⥤ C}

lemma wordAction_append (f : a ⟶ a') (g : b ⟶ b')
    (F : MovingDiagram D C W a A B) (G : MovingDiagram D C W b B E) :
    wordAction (Word.appendMap f g) (F.append G) = (wordAction f F).append (wordAction g G) := by
  apply ext
  · intro d
    exact ZigzagAppend.obj_naturality f g (F.obj d) (G.obj d)
  · intro d e h k
    exact ZigzagAppend.Moving.app_naturality f g (F.map h) (G.map h)
      ((F.last h).trans (G.first h).symm) k

end SerrePositivity.EInfinity.Hammock.Zigzag.MovingDiagram
