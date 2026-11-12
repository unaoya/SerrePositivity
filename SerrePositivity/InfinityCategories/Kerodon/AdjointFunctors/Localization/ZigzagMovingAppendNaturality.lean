module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendNaturalityArrows
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingWordAction
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingDiagramAppend
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingDiagramExt

/-!
# 動く全図式の連結と元の語の作用の自然性

概要：前後の局所端点も動く図式の連結と、元の語の圧縮を交換する。
方針：元の対象の連結自然性と cut の全縦成分の照合を使う。
規約：接合点の縦射も元の射を保持する。
使われ方：内部三列の圧縮を前後の全語へ拡張する。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v uD vD
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingAppendNaturality
open CategoryTheory

variable {C : Type u} [Category.{v} C] {W : MorphismProperty C} [W.IsMultiplicative]
  {a b a' b' : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} {X Y Z X' Y' Z' : C}
  {S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W a X Y} {S' : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W a X' Y'}
  {T : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W b Y Z} {T' : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W b Y' Z'}

lemma app_naturality (f : a ⟶ a') (g : b ⟶ b')
    (η : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingHom S S') (θ : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingHom T T')
    (hj : HEq (η.app (Fin.last a.length)) (θ.app 0))
    (k : Fin ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append a' b').length + 1)) :
    HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingAppendVertical.app η θ ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.appendMap f g).cut k))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingAppendVertical.app (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.movingMap f η) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.movingMap g θ) k) := by
  have hj' : HEq ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.movingMap f η).app (Fin.last a'.length))
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.movingMap g θ).app 0) :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingHom.app_heq η f.cut_last).trans
      (hj.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingHom.app_heq θ g.cut_zero).symm)
  by_cases hk : k.val ≤ a'.length
  · let i : Fin (a'.length + 1) := ⟨k.val, by omega⟩
    have hki : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.leftVertex a' b' i = k := Fin.ext rfl
    rw [← hki]
    exact ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingAppendVertical.app_index_heq η θ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.cut_append_left f g i)).trans
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingAppendVertical.app_left_heq η θ (f.cut i))).trans
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingAppendVertical.app_left_heq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.movingMap f η) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.movingMap g θ) i).symm
  · let i : Fin (b'.length + 1) := ⟨k.val - a'.length, by
      have h : k.val < a'.length + b'.length + 1 := k.isLt
      omega⟩
    have hki : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rightVertex a' b' i = k := Fin.ext (by dsimp [i, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rightVertex]; omega)
    rw [← hki]
    exact ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingAppendVertical.app_index_heq η θ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.cut_append_right f g i)).trans
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingAppendVertical.app_right_heq η θ hj (g.cut i))).trans
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingAppendVertical.app_right_heq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.movingMap f η) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.movingMap g θ) hj' i).symm

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingAppendNaturality
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingAppendNaturality
open CategoryTheory

variable {D : Type uD} [Category.{vD} D] {C : Type u} [Category.{v} C]
  {W : MorphismProperty C} [W.IsMultiplicative] {a b a' b' : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} {A B E : D ⥤ C}

lemma wordAction_append (f : a ⟶ a') (g : b ⟶ b')
    (F : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingDiagram D C W a A B) (G : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingDiagram D C W b B E) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.wordAction (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.appendMap f g) (F.append G) = (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.wordAction f F).append (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.wordAction g G) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ext
  · intro d
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.obj_naturality f g (F.obj d) (G.obj d)
  · intro d e h k
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingAppendNaturality.app_naturality f g (F.map h) (G.map h)
      ((F.last h).trans (G.first h).symm) k

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingDiagram export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingAppendNaturality (wordAction_append)


end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingAppendNaturality
