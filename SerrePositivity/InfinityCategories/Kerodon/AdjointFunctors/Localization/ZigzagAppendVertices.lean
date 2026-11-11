module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppendIndices

/-!
# 固定端点 zigzag の連結の全頂点

概要：二つの zigzag の共有端点を一つにして、連結語の全頂点を構成する。
方針：接合点までは左の頂点を使い、それ以降は右の頂点を使う。
規約：共有端点の同定は元の二つの端点の等式による。空語も含む。
使われ方：元の全列・全縦射を連結するための端点の移送。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendVertices
open CategoryTheory

variable {C : Type u} [Category.{v} C] {W : MorphismProperty C} {a b : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} {X Y Z : C}

/-- 接合点の左にある元の頂点の番号。 -/
def leftIndex (k : Fin ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append a b).length + 1)) (hk : k.val ≤ a.length) :
    Fin (a.length + 1) := ⟨k.val, by omega⟩

/-- 接合点より右にある元の頂点の番号。 -/
def rightIndex (k : Fin ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append a b).length + 1)) (hk : ¬ k.val ≤ a.length) :
    Fin (b.length + 1) :=
  ⟨k.val - a.length, by have h : k.val < a.length + b.length + 1 := k.isLt; omega⟩

/-- 接合点を一つだけ使う、元の二つの頂点列の連結。 -/
abbrev vertex (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W a X Y) (T : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W b Y Z)
    (k : Fin ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append a b).length + 1)) : C :=
  if hk : k.val ≤ a.length then S.vertex (leftIndex k hk) else T.vertex (rightIndex k hk)

lemma vertex_le (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W a X Y) (T : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W b Y Z)
    (k : Fin ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append a b).length + 1)) (hk : k.val ≤ a.length) :
    vertex S T k = S.vertex (leftIndex k hk) := dite_eq_left hk

lemma vertex_gt (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W a X Y) (T : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W b Y Z)
    (k : Fin ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append a b).length + 1)) (hk : ¬ k.val ≤ a.length) :
    vertex S T k = T.vertex (rightIndex k hk) := dite_eq_right hk

/-- 左部分の全頂点は、元の同じ左の頂点。 -/
lemma vertex_left (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W a X Y) (T : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W b Y Z) (i : Fin (a.length + 1)) :
    vertex S T (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.leftVertex a b i) = S.vertex i := by
  have hi : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.leftVertex a b i).val ≤ a.length := Nat.le_of_lt_succ i.isLt
  rw [vertex_le S T _ hi]
  rfl

/-- 右部分の全頂点は、元の同じ右の頂点。接合点の同定も含む。 -/
lemma vertex_right (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W a X Y) (T : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W b Y Z) (i : Fin (b.length + 1)) :
    vertex S T (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rightVertex a b i) = T.vertex i := by
  by_cases hi : i.val = 0
  · have h : i = 0 := Fin.ext hi
    subst i
    rw [vertex_le S T _ (by change a.length + 0 ≤ a.length; omega)]
    exact S.last.trans T.first.symm
  · rw [vertex_gt S T _ (by change ¬ a.length + i.val ≤ a.length; omega)]
    apply congrArg T.vertex
    apply Fin.ext
    dsimp [rightIndex, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rightVertex]
    omega

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendVertices
