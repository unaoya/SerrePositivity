module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.ZigzagAppendNaturalityArrows

/-!
# 元の連結関手と語の遷移の厳密な自然性

概要：連結してから圧縮する関手と、左右で圧縮してから連結する関手は厳密に等しい。
方針：全対象の同定と、元の切断位置での全縦射の同定を使う。
規約：自然同型だけで置き換えず、元の関手の等式を証明する。
使われ方：全語の graph の図式に自然な単体的合成。
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

/-- 連結と語の圧縮は、全縦射の元の同じ成分を回収する。 -/
lemma app_naturality (f : a ⟶ a') (g : b ⟶ b')
    {S S' : Zigzag W a X Y} {T T' : Zigzag W b Y Z} (η : S ⟶ S') (θ : T ⟶ T')
    (k : Fin ((Word.append a' b').length + 1)) :
    HEq ((WordAction.map (Word.appendMap f g) (map η θ)).app k)
      ((map (WordAction.map f η) (WordAction.map g θ)).app k) := by
  by_cases hk : k.val ≤ a'.length
  · let i : Fin (a'.length + 1) := ⟨k.val, by omega⟩
    have hki : Word.leftVertex a' b' i = k := Fin.ext rfl
    rw [← hki]
    exact ((app_index_heq η θ (Word.cut_append_left f g i)).trans
      (app_left_heq η θ (f.cut i))).trans
        (app_left_heq (WordAction.map f η) (WordAction.map g θ) i).symm
  · let i : Fin (b'.length + 1) := ⟨k.val - a'.length, by
      have h : k.val < a'.length + b'.length + 1 := k.isLt
      omega⟩
    have hki : Word.rightVertex a' b' i = k := Fin.ext (by dsimp [i, Word.rightVertex]; omega)
    rw [← hki]
    exact ((app_index_heq η θ (Word.cut_append_right f g i)).trans
      (app_right_heq η θ (g.cut i))).trans
        (app_right_heq (WordAction.map f η) (WordAction.map g θ) i).symm

/-- 元の連結関手と全語の遷移は、全対象・全縦弱同値で厳密に自然。 -/
lemma functor_naturality (f : a ⟶ a') (g : b ⟶ b') :
    functor (W := W) (a := a) (b := b) (X := X) (Y := Y) (Z := Z) ⋙
        WordAction.functor (Word.appendMap f g) =
      (WordAction.functor (W := W) (X := X) (Y := Y) f).prod
        (WordAction.functor (W := W) (X := Y) (Y := Z) g) ⋙ functor := by
  apply Functor.hext (fun p => obj_naturality f g p.1 p.2)
  intro p q h
  apply Zigzag.hom_hext (obj_naturality f g p.1 p.2) (obj_naturality f g q.1 q.2)
  intro k
  exact app_naturality f g h.1 h.2 k

end SerrePositivity.EInfinity.Hammock.ZigzagAppend
