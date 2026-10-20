module

public import SerrePositivity.EInfinity.Hammock.ZigzagAppendDirections
public import SerrePositivity.EInfinity.Hammock.WordAppendBlocks
public import SerrePositivity.EInfinity.Hammock.SegmentBlockComparison
public import SerrePositivity.EInfinity.Hammock.WordIdentity

/-!
# 連結の左右の区間合成の回収

概要：連結の左右の同方向区間の合成は、元の同じ部分の区間合成と異種等しい。
方針：連結の具体的な左右の連続部分へ、区間比較の定理を代入する。
規約：接合点と空区間も含む。モデル構造や射の類の乗法性は不要。
使われ方：連結と元の語の遷移の自然性。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.EInfinity.Hammock.ZigzagAppend
open CategoryTheory

variable {C : Type u} [Category.{v} C] {W : MorphismProperty C} {a b : Word} {X Y Z : C}

lemma arrow_index_heq {w : Word} {U V : C} (S : Zigzag W w U V) {i j : Fin w.length}
    (hij : i = j) : HEq (S.arrow i) (S.arrow j) := by
  cases hij
  rfl

/-- 左部分の区間合成は、元の左の同じ区間の合成と異種等しい。 -/
lemma map_left_heq (S : Zigzag W a X Y) (T : Zigzag W b Y Z) (d : Direction)
    (p q : Fin (a.length + 1)) (hpq : p ≤ q)
    (hd : ∀ i : Fin a.length, p.val ≤ i.val → i.val < q.val → a.direction i = d) :
    HEq (Segment.map d (obj S T) (Word.leftVertex a b p) (Word.leftVertex a b q)
      (Word.leftVertex_mono a b hpq) (Word.append_left_direction a b d p q hd))
      (Segment.map d S p q hpq hd) := by
  have hv := fun j => (congrArg (vertex S T) (Word.leftBlock_vertex a b j)).trans
    (vertex_left S T j)
  have ha := fun i => (arrow_index_heq (obj S T) (Word.leftBlock_column a b i)).trans
    (arrow_left_heq S T i)
  have h := WordAction.segment_heq_of_eq d (obj S T)
    (Word.leftBlock_vertex a b p).symm (Word.leftBlock_vertex a b q).symm
    (Word.leftVertex_mono a b hpq) ((Word.leftBlock a b).vertex_monotone hpq)
    (Word.append_left_direction a b d p q hd) ((Word.leftBlock a b).interval_direction d p q hd)
  exact h.trans (Segment.map_block_heq (Word.leftBlock a b) S (obj S T) hv ha d p q hpq hd)

/-- 右部分の区間合成も、接合点を含めて元の右の同じ区間の合成と異種等しい。 -/
lemma map_right_heq (S : Zigzag W a X Y) (T : Zigzag W b Y Z) (d : Direction)
    (p q : Fin (b.length + 1)) (hpq : p ≤ q)
    (hd : ∀ i : Fin b.length, p.val ≤ i.val → i.val < q.val → b.direction i = d) :
    HEq (Segment.map d (obj S T) (Word.rightVertex a b p) (Word.rightVertex a b q)
      (Word.rightVertex_mono a b hpq) (Word.append_right_direction a b d p q hd))
      (Segment.map d T p q hpq hd) :=
  Segment.map_block_heq (Word.rightBlock a b) T (obj S T) (vertex_right S T)
    (arrow_right_heq S T) d p q hpq hd

end SerrePositivity.EInfinity.Hammock.ZigzagAppend
