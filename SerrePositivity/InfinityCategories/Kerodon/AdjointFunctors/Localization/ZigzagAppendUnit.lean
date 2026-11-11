module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordUnit
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagWordTransport
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendFunctor
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Unit

/-!
# 空語の元の zigzag との連結の左右単位則

概要：空語の元の対象との連結は、語の単位等式に沿って元の zigzag と一致する。
方針：左右の全頂点・全列・全縦射の回収を使い、元の遷移関手と合成する。
規約：接合点の恒等条件は元の端点から導き、単位射を変更しない。
使われ方：全次数の graph の左右単位則と余極限への降下。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory

variable {C : Type u} [Category.{v} C] {W : MorphismProperty C} {a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} {X Y : C}

/-- 空語との左連結は元の全頂点・全列を回収する。 -/
lemma empty_left_obj_heq (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W a X Y) : HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.emptyObj W X) S) S := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.object_word_hext (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordUnit.empty_append a)
  · intro i j hij
    have h : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rightVertex _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.empty a j = i := Fin.ext (by
      dsimp [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rightVertex, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.empty]
      omega)
    exact (congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.emptyObj W X) S).vertex h).symm.trans
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendVertices.vertex_right (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.emptyObj W X) S j)
  · intro i j hij
    have h : j.natAdd 0 = i := Fin.ext (by simpa using hij.symm)
    rw [← h]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.arrow_right_heq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.emptyObj W X) S j

/-- 空語との右連結も元の全頂点・全列を回収する。 -/
lemma empty_right_obj_heq (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W a X Y) : HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.obj S (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.emptyObj W Y)) S := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.object_word_hext (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordUnit.append_empty a)
  · intro i j hij
    have h : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.leftVertex a _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.empty j = i := Fin.ext hij.symm
    exact (congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.obj S (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.emptyObj W Y)).vertex h).symm.trans
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendVertices.vertex_left S (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.emptyObj W Y) j)
  · intro i j hij
    have h : j.castAdd 0 = i := Fin.ext hij.symm
    rw [← h]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.arrow_left_heq S (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.emptyObj W Y) j

/-- 左の空語の恒等縦射との連結は、元の同じ全縦射を回収する。 -/
lemma empty_left_map_heq [W.IsMultiplicative] {S T : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W a X Y} (f : S ⟶ T) :
    HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendMorphisms.map (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.emptyObj W X)) f) f := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.hom_word_hext (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordUnit.empty_append a) (empty_left_obj_heq S)
    (empty_left_obj_heq T)
  intro i j hij
  have h : i = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rightVertex _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.empty a j := Fin.ext (by
    dsimp [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rightVertex, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.empty]
    omega)
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendVertical.app_index_heq (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.emptyObj W X)) f h).trans
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendVertical.app_right_heq (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.emptyObj W X)) f j)

/-- 右の空語の恒等縦射との連結も、元の同じ全縦射を回収する。 -/
lemma empty_right_map_heq [W.IsMultiplicative] {S T : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W a X Y} (f : S ⟶ T) :
    HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendMorphisms.map f (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.emptyObj W Y))) f := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.hom_word_hext (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordUnit.append_empty a) (empty_right_obj_heq S)
    (empty_right_obj_heq T)
  intro i j hij
  have h : i = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.leftVertex a _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.empty j := Fin.ext hij
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendVertical.app_index_heq f (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.emptyObj W Y)) h).trans
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendVertical.app_left_heq f (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.emptyObj W Y)) j)

/-- 空語の左連結と元の単位遷移は、恒等関手に厳密に一致する。 -/
lemma empty_left_functor [W.IsMultiplicative] :
    ((Functor.const (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W a X Y)).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.emptyObj W X)).prod' (𝟭 _) ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendFunctor.functor ⋙
        _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.functor (eqToHom (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordUnit.empty_append a)) = 𝟭 (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W a X Y) := by
  apply Functor.hext (fun S => eq_of_heq
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.obj_eqToHom_heq _ _).trans (empty_left_obj_heq S)))
  intro S T f
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.map_eqToHom_heq _ _).trans (empty_left_map_heq f)

/-- 空語の右連結と元の単位遷移も、恒等関手に厳密に一致する。 -/
lemma empty_right_functor [W.IsMultiplicative] :
    (𝟭 (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W a X Y)).prod' ((Functor.const _).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.emptyObj W Y)) ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendFunctor.functor ⋙
        _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.functor (eqToHom (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordUnit.append_empty a)) = 𝟭 (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W a X Y) := by
  apply Functor.hext (fun S => eq_of_heq
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.obj_eqToHom_heq _ _).trans (empty_right_obj_heq S)))
  intro S T f
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.map_eqToHom_heq _ _).trans (empty_right_map_heq f)

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
