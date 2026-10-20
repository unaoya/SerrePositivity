module

public import SerrePositivity.EInfinity.Hammock.ZigzagAppendNaturalityVertices
public import SerrePositivity.EInfinity.Hammock.ZigzagAppendSegments
public import SerrePositivity.EInfinity.Hammock.DirectionArrowReflection

/-!
# 連結と語の遷移の全列での整合

概要：連結してから圧縮する場合と、左右で圧縮してから連結する場合の全列を照合。
方針：左右の切断公式と区間合成の回収を、向きに応じた圏で合成する。
規約：最後に元の圏の列へ戻す。局所化後だけの一致で置き換えない。
使われ方：連結と元の語の遷移の厳密な自然性。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.EInfinity.Hammock.ZigzagAppend
open CategoryTheory

variable {C : Type u} [Category.{v} C] {W : MorphismProperty C} [W.IsMultiplicative]
  {a b a' b' : Word} {X Y Z : C}

lemma direction_naturality_left (f : a ⟶ a') (g : b ⟶ b')
    (S : Zigzag W a X Y) (T : Zigzag W b Y Z) (i : Fin a'.length) :
    HEq (Direction.arrow (a'.direction i) (WordAction.obj (Word.appendMap f g) (obj S T))
      (i.castAdd b'.length) (Word.append_direction_left a' b' i))
      (Direction.arrow (a'.direction i) (obj (WordAction.obj f S) (WordAction.obj g T))
        (i.castAdd b'.length) (Word.append_direction_left a' b' i)) := by
  let hd := fun j hj hj' => f.fiber_direction i j hj hj'
  have he := WordAction.segment_heq_of_eq (a'.direction i) (obj S T)
    (Word.cut_append_left f g i.castSucc) (Word.cut_append_left f g i.succ)
    ((Word.appendMap f g).cut_monotone (Fin.castSucc_le_succ (i.castAdd b'.length)))
    (Word.leftVertex_mono a b (f.cut_monotone (Fin.castSucc_le_succ i)))
    (fun j hj hj' => ((Word.appendMap f g).fiber_direction (i.castAdd b'.length) j hj hj').trans
      (Word.append_direction_left a' b' i))
    (Word.append_left_direction a b _ (f.cut i.castSucc) (f.cut i.succ) hd)
  have hl := (WordAction.arrow_obj_heq (Word.appendMap f g) (obj S T) _ _
    (Word.append_direction_left a' b' i)).trans
      (he.trans (map_left_heq S T (a'.direction i) (f.cut i.castSucc) (f.cut i.succ)
        (f.cut_monotone (Fin.castSucc_le_succ i)) hd))
  exact hl.trans ((WordAction.arrow_obj_heq f S _ i rfl).symm.trans
    (direction_left_heq (WordAction.obj f S) (WordAction.obj g T) _ i rfl).symm)

lemma direction_naturality_right (f : a ⟶ a') (g : b ⟶ b')
    (S : Zigzag W a X Y) (T : Zigzag W b Y Z) (i : Fin b'.length) :
    HEq (Direction.arrow (b'.direction i) (WordAction.obj (Word.appendMap f g) (obj S T))
      (i.natAdd a'.length) (Word.append_direction_right a' b' i))
      (Direction.arrow (b'.direction i) (obj (WordAction.obj f S) (WordAction.obj g T))
        (i.natAdd a'.length) (Word.append_direction_right a' b' i)) := by
  let hd := fun j hj hj' => g.fiber_direction i j hj hj'
  have he := WordAction.segment_heq_of_eq (b'.direction i) (obj S T)
    (Word.cut_append_right f g i.castSucc) (Word.cut_append_right f g i.succ)
    ((Word.appendMap f g).cut_monotone (Fin.castSucc_le_succ (i.natAdd a'.length)))
    (Word.rightVertex_mono a b (g.cut_monotone (Fin.castSucc_le_succ i)))
    (fun j hj hj' => ((Word.appendMap f g).fiber_direction (i.natAdd a'.length) j hj hj').trans
      (Word.append_direction_right a' b' i))
    (Word.append_right_direction a b _ (g.cut i.castSucc) (g.cut i.succ) hd)
  have hl := (WordAction.arrow_obj_heq (Word.appendMap f g) (obj S T) _ _
    (Word.append_direction_right a' b' i)).trans
      (he.trans (map_right_heq S T (b'.direction i) (g.cut i.castSucc) (g.cut i.succ)
        (g.cut_monotone (Fin.castSucc_le_succ i)) hd))
  exact hl.trans ((WordAction.arrow_obj_heq g T _ i rfl).symm.trans
    (direction_right_heq (WordAction.obj f S) (WordAction.obj g T) _ i rfl).symm)

/-- 元の全列でも、連結と語の圧縮は同じ射を与える。 -/
lemma arrow_naturality (f : a ⟶ a') (g : b ⟶ b') (S : Zigzag W a X Y) (T : Zigzag W b Y Z)
    (i : Fin (Word.append a' b').length) :
    HEq ((WordAction.obj (Word.appendMap f g) (obj S T)).arrow i)
      ((obj (WordAction.obj f S) (WordAction.obj g T)).arrow i) := by
  cases i using Fin.addCases with
  | left i =>
    exact Direction.raw_arrow_heq_of _ _ (a'.direction i) _ _
      (Word.append_direction_left a' b' i) (Word.append_direction_left a' b' i)
      (vertex_naturality f g S T _) (vertex_naturality f g S T _)
      (direction_naturality_left f g S T i)
  | right i =>
    exact Direction.raw_arrow_heq_of _ _ (b'.direction i) _ _
      (Word.append_direction_right a' b' i) (Word.append_direction_right a' b' i)
      (vertex_naturality f g S T _) (vertex_naturality f g S T _)
      (direction_naturality_right f g S T i)

/-- 連結と語の圧縮は、元の全対象で厳密に一致する。 -/
lemma obj_naturality (f : a ⟶ a') (g : b ⟶ b') (S : Zigzag W a X Y) (T : Zigzag W b Y Z) :
    WordAction.obj (Word.appendMap f g) (obj S T) =
      obj (WordAction.obj f S) (WordAction.obj g T) :=
  Zigzag.object_ext _ _ (vertex_naturality f g S T) (arrow_naturality f g S T)

end SerrePositivity.EInfinity.Hammock.ZigzagAppend
