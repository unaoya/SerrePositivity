module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordInsertBetweenCut
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordEmbeddingObjects
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordPlateauColumn
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.BackwardZigzag
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects

/-!
# 中央 backward 恒等列を持つ元の連結対象

概要：左右の元の zigzag の間に同じ接合対象の恒等列を置く。
方針：元の連結の全成分を回収し、像の外の列を元の恒等射へ照合する。
規約：元の対象・射を保持する。両方の語が空でもよい。
使われ方：語の作用の像と右置換の実際の対象を照合する。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InsertBetweenObjects
open CategoryTheory

variable {C : Type u} [Category.{v} C] {W : MorphismProperty C} [W.IsMultiplicative]
  {a b : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} {X E Y : C} (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W a X E) (T : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W b E Y)

def obj : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append a (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .backward)) b) X Y :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.obj S (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.BackwardZigzag.obj (𝟙 E) (W.id_mem _))) T

lemma obj_leftVertex (i : Fin (a.length + 1)) :
    (obj S T).vertex (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.leftVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append a (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .backward)) b
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.leftVertex a (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .backward) i)) = S.vertex i := by
  simp only [obj, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.obj, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendVertices.vertex_left]

lemma obj_rightVertex (i : Fin (b.length + 1)) :
    (obj S T).vertex (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rightVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append a (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .backward)) b i) =
      T.vertex i := by
  simp only [obj, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.obj, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendVertices.vertex_right]

lemma action_leftVertex (i : Fin (a.length + 1)) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.insertBetween a b .backward) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.obj S T)).vertex
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.leftVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append a (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .backward)) b
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.leftVertex a (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .backward) i)) = S.vertex i := by
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.obj S T).vertex ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.insertBetween a b .backward).cut _) = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.insertBetween_cut_leftVertex]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendVertices.vertex_left S T i

lemma action_rightVertex (i : Fin (b.length + 1)) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.insertBetween a b .backward) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.obj S T)).vertex
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rightVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append a (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .backward)) b i) = T.vertex i := by
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.obj S T).vertex ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.insertBetween a b .backward).cut _) = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.insertBetween_cut_rightVertex]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendVertices.vertex_right S T i

lemma obj_arrow_left_heq (i : Fin a.length) :
    HEq ((obj S T).arrow ((i.castAdd 1).castAdd b.length)) (S.arrow i) := by
  dsimp only [obj]
  apply HEq.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.arrow_left_heq (b := b) _ _ _)
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.arrow_left_heq S _ i

lemma obj_arrow_right_heq (i : Fin b.length) :
    HEq ((obj S T).arrow (i.natAdd (a.length + 1))) (T.arrow i) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.arrow_right_heq _ T i

lemma obj_arrow_middle_heq :
    HEq ((obj S T).arrow (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.insertedColumn a b .backward)) (𝟙 E) := by
  dsimp only [obj, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.insertedColumn]
  apply HEq.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.arrow_left_heq (b := b) _ _ _)
  apply HEq.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.arrow_right_heq (a := a) _ _ _)
  rfl

lemma action_arrow_middle_heq :
    HEq ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.insertBetween a b .backward) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.obj S T)).arrow
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.insertedColumn a b .backward)) (𝟙 E) := by
  let f := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.insertBetween a b .backward
  let j := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.insertedColumn a b .backward
  let V := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.obj S T
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.insertBetween_cut_inserted a b .backward
  have he := f.cut_source_target_of_eq j h
  change HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.column f V j) (𝟙 E)
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.column_eqToHom_of_cut_eq f V j h he]
  apply HEq.trans (eqToHom_heq_id_dom _ _ (congrArg V.vertex he))
  have hs : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append a (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .backward)) b).source j =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rightVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append a (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .backward)) b 0 := by
    unfold _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.source
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.insertedColumn_direction]
    apply Fin.ext
    simp [j, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.insertedColumn, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rightVertex, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single]
  have hv : V.vertex (f.cut ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append a (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .backward)) b).source j)) =
      E := by
    rw [hs, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.insertBetween_cut_rightVertex]
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendVertices.vertex_right S T 0).trans T.first
  exact (eqToHom_heq_id_dom _ _ hv).symm.trans (eqToHom_heq_id_cod _ _ hv)

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InsertBetweenObjects
