module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.ZigzagAppendFunctor
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.WordAppendCut
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.WordComposition

/-!
# 連結と語の遷移の全頂点での整合

概要：連結してから圧縮する場合と、左右で圧縮してから連結する場合の全頂点を照合。
方針：元の左右の切断公式と、連結の左右の頂点の回収を使う。
規約：接合点を含む全頂点。元の対象を別の置換へ変更しない。
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

/-- 連結と語の遷移は、接合点を含む全頂点で同じ元の対象を与える。 -/
lemma vertex_naturality (f : a ⟶ a') (g : b ⟶ b') (S : Zigzag W a X Y) (T : Zigzag W b Y Z)
    (k : Fin ((Word.append a' b').length + 1)) :
    (WordAction.obj (Word.appendMap f g) (obj S T)).vertex k =
      (obj (WordAction.obj f S) (WordAction.obj g T)).vertex k := by
  by_cases hk : k.val ≤ a'.length
  · let i : Fin (a'.length + 1) := ⟨k.val, by omega⟩
    have hki : Word.leftVertex a' b' i = k := Fin.ext rfl
    rw [← hki]
    exact ((congrArg (vertex S T) (Word.cut_append_left f g i)).trans
      (vertex_left S T (f.cut i))).trans
        (vertex_left (WordAction.obj f S) (WordAction.obj g T) i).symm
  · let i : Fin (b'.length + 1) := ⟨k.val - a'.length, by
      have h : k.val < a'.length + b'.length + 1 := k.isLt
      omega⟩
    have hki : Word.rightVertex a' b' i = k := Fin.ext (by dsimp [i, Word.rightVertex]; omega)
    rw [← hki]
    exact ((congrArg (vertex S T) (Word.cut_append_right f g i)).trans
      (vertex_right S T (g.cut i))).trans
        (vertex_right (WordAction.obj f S) (WordAction.obj g T) i).symm

end SerrePositivity.EInfinity.Hammock.ZigzagAppend
