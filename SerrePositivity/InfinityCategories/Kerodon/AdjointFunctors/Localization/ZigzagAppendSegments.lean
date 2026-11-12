module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendDirections
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppendBlocks
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.SegmentBlockComparison
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordIdentity

/-!
# 連結の左右の区間合成の回収

概要：連結の左右の同方向区間の合成は、元の同じ部分の区間合成と異種等しい。
方針：連結の具体的な左右の連続部分へ、区間比較の定理を代入する。
規約：接合点と空区間も含む。モデル構造や射の類の乗法性は不要。
使われ方：連結と元の語の遷移の自然性。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory

variable {C : Type u} [Category.{v} C] {W : MorphismProperty C} {a b : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} {X Y Z : C}

lemma arrow_index_heq {w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} {U V : C} (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W w U V) {i j : Fin w.length}
    (hij : i = j) : HEq (S.arrow i) (S.arrow j) := by
  cases hij
  rfl

/-- 左部分の区間合成は、元の左の同じ区間の合成と異種等しい。 -/
lemma map_left_heq (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W a X Y) (T : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W b Y Z) (d : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Direction)
    (p q : Fin (a.length + 1)) (hpq : p ≤ q)
    (hd : ∀ i : Fin a.length, p.val ≤ i.val → i.val < q.val → a.direction i = d) :
    HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Segment.map d (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.obj S T) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.leftVertex a b p) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.leftVertex a b q)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.leftVertex_mono a b hpq) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.append_left_direction a b d p q hd))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Segment.map d S p q hpq hd) := by
  have hv := fun j => (congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendVertices.vertex S T) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppendBlocks.leftBlock_vertex a b j)).trans
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendVertices.vertex_left S T j)
  have ha := fun i => (arrow_index_heq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.obj S T) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppendBlocks.leftBlock_column a b i)).trans
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.arrow_left_heq S T i)
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.segment_heq_of_eq d (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.obj S T)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppendBlocks.leftBlock_vertex a b p).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppendBlocks.leftBlock_vertex a b q).symm
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.leftVertex_mono a b hpq) ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppendBlocks.leftBlock a b).vertex_monotone hpq)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.append_left_direction a b d p q hd) ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppendBlocks.leftBlock a b).interval_direction d p q hd)
  exact h.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.map_block_heq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppendBlocks.leftBlock a b) S (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.obj S T) hv ha d p q hpq hd)

/-- 右部分の区間合成も、接合点を含めて元の右の同じ区間の合成と異種等しい。 -/
lemma map_right_heq (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W a X Y) (T : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W b Y Z) (d : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Direction)
    (p q : Fin (b.length + 1)) (hpq : p ≤ q)
    (hd : ∀ i : Fin b.length, p.val ≤ i.val → i.val < q.val → b.direction i = d) :
    HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Segment.map d (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.obj S T) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rightVertex a b p) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rightVertex a b q)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rightVertex_mono a b hpq) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.append_right_direction a b d p q hd))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Segment.map d T p q hpq hd) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.map_block_heq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppendBlocks.rightBlock a b) T (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.obj S T) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendVertices.vertex_right S T)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.arrow_right_heq S T) d p q hpq hd

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
