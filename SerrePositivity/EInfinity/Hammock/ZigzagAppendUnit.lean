module

public import SerrePositivity.EInfinity.Hammock.WordUnit
public import SerrePositivity.EInfinity.Hammock.ZigzagWordTransport
public import SerrePositivity.EInfinity.Hammock.ZigzagAppendFunctor
public import SerrePositivity.EInfinity.Hammock.Unit

/-!
# 空語の元の zigzag との連結の左右単位則

概要：空語の元の対象との連結は、語の単位等式に沿って元の zigzag と一致する。
方針：左右の全頂点・全列・全縦射の回収を使い、元の遷移関手と合成する。
規約：接合点の恒等条件は元の端点から導き、単位射を変更しない。
使われ方：全次数の graph の左右単位則と余極限への降下。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.EInfinity.Hammock.ZigzagAppend
open CategoryTheory

variable {C : Type u} [Category.{v} C] {W : MorphismProperty C} {a : Word} {X Y : C}

/-- 空語との左連結は元の全頂点・全列を回収する。 -/
lemma empty_left_obj_heq (S : Zigzag W a X Y) : HEq (obj (emptyObj W X) S) S := by
  apply Zigzag.object_word_hext (Word.empty_append a)
  · intro i j hij
    have h : Word.rightVertex Word.empty a j = i := Fin.ext (by
      dsimp [Word.rightVertex, Word.empty]
      omega)
    exact (congrArg (obj (emptyObj W X) S).vertex h).symm.trans
      (vertex_right (emptyObj W X) S j)
  · intro i j hij
    have h : j.natAdd 0 = i := Fin.ext (by simpa using hij.symm)
    rw [← h]
    exact arrow_right_heq (emptyObj W X) S j

/-- 空語との右連結も元の全頂点・全列を回収する。 -/
lemma empty_right_obj_heq (S : Zigzag W a X Y) : HEq (obj S (emptyObj W Y)) S := by
  apply Zigzag.object_word_hext (Word.append_empty a)
  · intro i j hij
    have h : Word.leftVertex a Word.empty j = i := Fin.ext hij.symm
    exact (congrArg (obj S (emptyObj W Y)).vertex h).symm.trans
      (vertex_left S (emptyObj W Y) j)
  · intro i j hij
    have h : j.castAdd 0 = i := Fin.ext hij.symm
    rw [← h]
    exact arrow_left_heq S (emptyObj W Y) j

/-- 左の空語の恒等縦射との連結は、元の同じ全縦射を回収する。 -/
lemma empty_left_map_heq [W.IsMultiplicative] {S T : Zigzag W a X Y} (f : S ⟶ T) :
    HEq (map (𝟙 (emptyObj W X)) f) f := by
  apply Zigzag.hom_word_hext (Word.empty_append a) (empty_left_obj_heq S)
    (empty_left_obj_heq T)
  intro i j hij
  have h : i = Word.rightVertex Word.empty a j := Fin.ext (by
    dsimp [Word.rightVertex, Word.empty]
    omega)
  exact (app_index_heq (𝟙 (emptyObj W X)) f h).trans
    (app_right_heq (𝟙 (emptyObj W X)) f j)

/-- 右の空語の恒等縦射との連結も、元の同じ全縦射を回収する。 -/
lemma empty_right_map_heq [W.IsMultiplicative] {S T : Zigzag W a X Y} (f : S ⟶ T) :
    HEq (map f (𝟙 (emptyObj W Y))) f := by
  apply Zigzag.hom_word_hext (Word.append_empty a) (empty_right_obj_heq S)
    (empty_right_obj_heq T)
  intro i j hij
  have h : i = Word.leftVertex a Word.empty j := Fin.ext hij
  exact (app_index_heq f (𝟙 (emptyObj W Y)) h).trans
    (app_left_heq f (𝟙 (emptyObj W Y)) j)

/-- 空語の左連結と元の単位遷移は、恒等関手に厳密に一致する。 -/
lemma empty_left_functor [W.IsMultiplicative] :
    ((Functor.const (Zigzag W a X Y)).obj (emptyObj W X)).prod' (𝟭 _) ⋙ functor ⋙
        WordAction.functor (eqToHom (Word.empty_append a)) = 𝟭 (Zigzag W a X Y) := by
  apply Functor.hext (fun S => eq_of_heq
    ((WordAction.obj_eqToHom_heq _ _).trans (empty_left_obj_heq S)))
  intro S T f
  exact (WordAction.map_eqToHom_heq _ _).trans (empty_left_map_heq f)

/-- 空語の右連結と元の単位遷移も、恒等関手に厳密に一致する。 -/
lemma empty_right_functor [W.IsMultiplicative] :
    (𝟭 (Zigzag W a X Y)).prod' ((Functor.const _).obj (emptyObj W Y)) ⋙ functor ⋙
        WordAction.functor (eqToHom (Word.append_empty a)) = 𝟭 (Zigzag W a X Y) := by
  apply Functor.hext (fun S => eq_of_heq
    ((WordAction.obj_eqToHom_heq _ _).trans (empty_right_obj_heq S)))
  intro S T f
  exact (WordAction.map_eqToHom_heq _ _).trans (empty_right_map_heq f)

end SerrePositivity.EInfinity.Hammock.ZigzagAppend
