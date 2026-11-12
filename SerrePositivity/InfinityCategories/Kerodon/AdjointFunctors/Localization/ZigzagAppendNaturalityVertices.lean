module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendFunctor
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppendCut
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordComposition

/-!
# 連結と語の遷移の全頂点での整合

概要：連結してから圧縮する場合と、左右で圧縮してから連結する場合の全頂点を照合。
方針：元の左右の切断公式と、連結の左右の頂点の回収を使う。
規約：接合点を含む全頂点。元の対象を別の置換へ変更しない。
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

/-- 連結と語の遷移は、接合点を含む全頂点で同じ元の対象を与える。 -/
lemma vertex_naturality (f : a ⟶ a') (g : b ⟶ b') (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W a X Y) (T : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W b Y Z)
    (k : Fin ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append a' b').length + 1)) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.appendMap f g) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.obj S T)).vertex k =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.obj f S) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.obj g T)).vertex k := by
  by_cases hk : k.val ≤ a'.length
  · let i : Fin (a'.length + 1) := ⟨k.val, by omega⟩
    have hki : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.leftVertex a' b' i = k := Fin.ext rfl
    rw [← hki]
    exact ((congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendVertices.vertex S T) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.cut_append_left f g i)).trans
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendVertices.vertex_left S T (f.cut i))).trans
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendVertices.vertex_left (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.obj f S) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.obj g T) i).symm
  · let i : Fin (b'.length + 1) := ⟨k.val - a'.length, by
      have h : k.val < a'.length + b'.length + 1 := k.isLt
      omega⟩
    have hki : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rightVertex a' b' i = k := Fin.ext (by dsimp [i, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rightVertex]; omega)
    rw [← hki]
    exact ((congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendVertices.vertex S T) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.cut_append_right f g i)).trans
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendVertices.vertex_right S T (g.cut i))).trans
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendVertices.vertex_right (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.obj f S) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.obj g T) i).symm

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
