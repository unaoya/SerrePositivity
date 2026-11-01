module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.WordInsertBetweenCut
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.WordEmbeddingObjects
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.WordPlateauColumn
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.BackwardZigzag
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.ZigzagAppendObjects

/-!
# 中央 backward 恒等列を持つ元の連結対象

概要：左右の元の zigzag の間に同じ接合対象の恒等列を置く。
方針：元の連結の全成分を回収し、像の外の列を元の恒等射へ照合する。
規約：元の対象・射を保持する。両方の語が空でもよい。
使われ方：語の作用の像と右置換の実際の対象を照合する。
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

def obj : Zigzag W (Word.append (Word.append a (Word.single .backward)) b) X Y :=
  ZigzagAppend.obj (ZigzagAppend.obj S (BackwardZigzag.obj (𝟙 E) (W.id_mem _))) T

lemma obj_leftVertex (i : Fin (a.length + 1)) :
    (obj S T).vertex (Word.leftVertex (Word.append a (Word.single .backward)) b
      (Word.leftVertex a (Word.single .backward) i)) = S.vertex i := by
  simp only [obj, ZigzagAppend.obj, ZigzagAppend.vertex_left]

lemma obj_rightVertex (i : Fin (b.length + 1)) :
    (obj S T).vertex (Word.rightVertex (Word.append a (Word.single .backward)) b i) =
      T.vertex i := by
  simp only [obj, ZigzagAppend.obj, ZigzagAppend.vertex_right]

lemma action_leftVertex (i : Fin (a.length + 1)) :
    (WordAction.obj (Word.insertBetween a b .backward) (ZigzagAppend.obj S T)).vertex
      (Word.leftVertex (Word.append a (Word.single .backward)) b
        (Word.leftVertex a (Word.single .backward) i)) = S.vertex i := by
  change (ZigzagAppend.obj S T).vertex ((Word.insertBetween a b .backward).cut _) = _
  rw [Word.insertBetween_cut_leftVertex]
  exact ZigzagAppend.vertex_left S T i

lemma action_rightVertex (i : Fin (b.length + 1)) :
    (WordAction.obj (Word.insertBetween a b .backward) (ZigzagAppend.obj S T)).vertex
      (Word.rightVertex (Word.append a (Word.single .backward)) b i) = T.vertex i := by
  change (ZigzagAppend.obj S T).vertex ((Word.insertBetween a b .backward).cut _) = _
  rw [Word.insertBetween_cut_rightVertex]
  exact ZigzagAppend.vertex_right S T i

lemma obj_arrow_left_heq (i : Fin a.length) :
    HEq ((obj S T).arrow ((i.castAdd 1).castAdd b.length)) (S.arrow i) := by
  dsimp only [obj]
  apply HEq.trans (ZigzagAppend.arrow_left_heq (b := b) _ _ _)
  exact ZigzagAppend.arrow_left_heq S _ i

lemma obj_arrow_right_heq (i : Fin b.length) :
    HEq ((obj S T).arrow (i.natAdd (a.length + 1))) (T.arrow i) :=
  ZigzagAppend.arrow_right_heq _ T i

lemma obj_arrow_middle_heq :
    HEq ((obj S T).arrow (Word.insertedColumn a b .backward)) (𝟙 E) := by
  dsimp only [obj, Word.insertedColumn]
  apply HEq.trans (ZigzagAppend.arrow_left_heq (b := b) _ _ _)
  apply HEq.trans (ZigzagAppend.arrow_right_heq (a := a) _ _ _)
  rfl

lemma action_arrow_middle_heq :
    HEq ((WordAction.obj (Word.insertBetween a b .backward) (ZigzagAppend.obj S T)).arrow
      (Word.insertedColumn a b .backward)) (𝟙 E) := by
  let f := Word.insertBetween a b .backward
  let j := Word.insertedColumn a b .backward
  let V := ZigzagAppend.obj S T
  have h := Word.insertBetween_cut_inserted a b .backward
  have he := f.cut_source_target_of_eq j h
  change HEq (WordAction.column f V j) (𝟙 E)
  rw [WordAction.column_eqToHom_of_cut_eq f V j h he]
  apply HEq.trans (eqToHom_heq_id_dom _ _ (congrArg V.vertex he))
  have hs : (Word.append (Word.append a (Word.single .backward)) b).source j =
      Word.rightVertex (Word.append a (Word.single .backward)) b 0 := by
    unfold Word.source
    rw [Word.insertedColumn_direction]
    apply Fin.ext
    simp [j, Word.insertedColumn, Word.rightVertex, Word.single]
  have hv : V.vertex (f.cut ((Word.append (Word.append a (Word.single .backward)) b).source j)) =
      E := by
    rw [hs, Word.insertBetween_cut_rightVertex]
    exact (ZigzagAppend.vertex_right S T 0).trans T.first
  exact (eqToHom_heq_id_dom _ _ hv).symm.trans (eqToHom_heq_id_cod _ _ hv)

end SerrePositivity.EInfinity.Hammock.InsertBetween
