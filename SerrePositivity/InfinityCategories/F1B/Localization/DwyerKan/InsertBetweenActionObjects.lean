module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.InsertBetweenObjects

/-!
# 元の語の作用による中央恒等列の挿入の対象の同定

概要：元の insertBetween の WordAction は、元の左右対象の間に恒等列を置く対象。
方針：切断による全頂点、像の全列、像の外の一列を元の射で照合する。
規約：語の長さだけや nerve のホモトピーだけで同定しない。
使われ方：右置換の各対象が元の語の作用の本質像に属することの証拠。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.InsertBetween
open CategoryTheory

variable {C : Type u} [Category.{v} C] {W : MorphismProperty C} [W.IsMultiplicative]
  {a b : Word} {X E Y : C} (S : Zigzag W a X E) (T : Zigzag W b E Y)

lemma action_obj_eq :
    WordAction.obj (Word.insertBetween a b .backward) (ZigzagAppend.obj S T) = obj S T := by
  apply Zigzag.object_ext
  · intro j
    apply Word.insertBetween_vertex_cases a b .backward
      (P := fun j => (WordAction.obj (Word.insertBetween a b .backward)
        (ZigzagAppend.obj S T)).vertex j = (obj S T).vertex j)
    · intro i
      exact (action_leftVertex S T i).trans (obj_leftVertex S T i).symm
    · intro i
      exact (action_rightVertex S T i).trans (obj_rightVertex S T i).symm
  · intro j
    apply Word.insertBetween_column_cases a b .backward
      (P := fun j => HEq ((WordAction.obj (Word.insertBetween a b .backward)
        (ZigzagAppend.obj S T)).arrow j) ((obj S T).arrow j))
    · intro i
      have h := WordAction.arrow_image_heq (Word.insertBetween a b .backward)
        (Word.insertBetween_injective a b .backward) (ZigzagAppend.obj S T) (i.castAdd b.length)
      rw [Word.insertBetween_left] at h
      exact (h.trans (ZigzagAppend.arrow_left_heq S T i)).trans (obj_arrow_left_heq S T i).symm
    · exact (action_arrow_middle_heq S T).trans (obj_arrow_middle_heq S T).symm
    · intro i
      have h := WordAction.arrow_image_heq (Word.insertBetween a b .backward)
        (Word.insertBetween_injective a b .backward) (ZigzagAppend.obj S T) (i.natAdd a.length)
      rw [Word.insertBetween_right] at h
      exact (h.trans (ZigzagAppend.arrow_right_heq S T i)).trans (obj_arrow_right_heq S T i).symm

end SerrePositivity.EInfinity.Hammock.InsertBetween
