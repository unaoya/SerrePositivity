module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendNaturalityVertices
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendSegments
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DirectionArrowReflection

/-!
# 連結と語の遷移の全列での整合

概要：連結してから圧縮する場合と、左右で圧縮してから連結する場合の全列を照合。
方針：左右の切断公式と区間合成の回収を、向きに応じた圏で合成する。
規約：最後に元の圏の列へ戻す。局所化後だけの一致で置き換えない。
使われ方：連結と元の語の遷移の厳密な自然性。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory

variable {C : Type u} [Category.{v} C] {W : MorphismProperty C} [W.IsMultiplicative]
  {a b a' b' : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} {X Y Z : C}

lemma direction_naturality_left (f : a ⟶ a') (g : b ⟶ b')
    (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W a X Y) (T : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W b Y Z) (i : Fin a'.length) :
    HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DirectionCategory.arrow (a'.direction i) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.appendMap f g) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.obj S T))
      (i.castAdd b'.length) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append_direction_left a' b' i))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DirectionCategory.arrow (a'.direction i) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.obj f S) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.obj g T))
        (i.castAdd b'.length) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append_direction_left a' b' i)) := by
  let hd := fun j hj hj' => f.fiber_direction i j hj hj'
  have he := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.segment_heq_of_eq (a'.direction i) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.obj S T)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.cut_append_left f g i.castSucc) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.cut_append_left f g i.succ)
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.appendMap f g).cut_monotone (Fin.castSucc_le_succ (i.castAdd b'.length)))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.leftVertex_mono a b (f.cut_monotone (Fin.castSucc_le_succ i)))
    (fun j hj hj' => ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.appendMap f g).fiber_direction (i.castAdd b'.length) j hj hj').trans
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append_direction_left a' b' i))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.append_left_direction a b _ (f.cut i.castSucc) (f.cut i.succ) hd)
  have hl := (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrow_obj_heq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.appendMap f g) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.obj S T) _ _
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append_direction_left a' b' i)).trans
      (he.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.map_left_heq S T (a'.direction i) (f.cut i.castSucc) (f.cut i.succ)
        (f.cut_monotone (Fin.castSucc_le_succ i)) hd))
  exact hl.trans ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrow_obj_heq f S _ i rfl).symm.trans
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.direction_left_heq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.obj f S) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.obj g T) _ i rfl).symm)

lemma direction_naturality_right (f : a ⟶ a') (g : b ⟶ b')
    (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W a X Y) (T : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W b Y Z) (i : Fin b'.length) :
    HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DirectionCategory.arrow (b'.direction i) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.appendMap f g) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.obj S T))
      (i.natAdd a'.length) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append_direction_right a' b' i))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DirectionCategory.arrow (b'.direction i) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.obj f S) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.obj g T))
        (i.natAdd a'.length) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append_direction_right a' b' i)) := by
  let hd := fun j hj hj' => g.fiber_direction i j hj hj'
  have he := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.segment_heq_of_eq (b'.direction i) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.obj S T)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.cut_append_right f g i.castSucc) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.cut_append_right f g i.succ)
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.appendMap f g).cut_monotone (Fin.castSucc_le_succ (i.natAdd a'.length)))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rightVertex_mono a b (g.cut_monotone (Fin.castSucc_le_succ i)))
    (fun j hj hj' => ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.appendMap f g).fiber_direction (i.natAdd a'.length) j hj hj').trans
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append_direction_right a' b' i))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.append_right_direction a b _ (g.cut i.castSucc) (g.cut i.succ) hd)
  have hl := (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrow_obj_heq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.appendMap f g) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.obj S T) _ _
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append_direction_right a' b' i)).trans
      (he.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.map_right_heq S T (b'.direction i) (g.cut i.castSucc) (g.cut i.succ)
        (g.cut_monotone (Fin.castSucc_le_succ i)) hd))
  exact hl.trans ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrow_obj_heq g T _ i rfl).symm.trans
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.direction_right_heq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.obj f S) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.obj g T) _ i rfl).symm)

/-- 元の全列でも、連結と語の圧縮は同じ射を与える。 -/
lemma arrow_naturality (f : a ⟶ a') (g : b ⟶ b') (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W a X Y) (T : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W b Y Z)
    (i : Fin (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append a' b').length) :
    HEq ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.appendMap f g) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.obj S T)).arrow i)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.obj f S) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.obj g T)).arrow i) := by
  cases i using Fin.addCases with
  | left i =>
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.raw_arrow_heq_of _ _ (a'.direction i) _ _
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append_direction_left a' b' i) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append_direction_left a' b' i)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.vertex_naturality f g S T _) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.vertex_naturality f g S T _)
      (direction_naturality_left f g S T i)
  | right i =>
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.raw_arrow_heq_of _ _ (b'.direction i) _ _
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append_direction_right a' b' i) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append_direction_right a' b' i)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.vertex_naturality f g S T _) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.vertex_naturality f g S T _)
      (direction_naturality_right f g S T i)

/-- 連結と語の圧縮は、元の全対象で厳密に一致する。 -/
lemma obj_naturality (f : a ⟶ a') (g : b ⟶ b') (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W a X Y) (T : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W b Y Z) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.appendMap f g) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.obj S T) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.obj f S) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.obj g T) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagExt.object_ext _ _ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.vertex_naturality f g S T) (arrow_naturality f g S T)

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
