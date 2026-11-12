module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Segment

/-!
# 同方向の区間の合成可能射列の制限

概要：小さい連続区間の射列を、大きい区間の射列の元の制限と同定する。
方針：区間内の位置の単調写像を作り、全頂点と隣接射を照合する。
規約：同型や局所化だけでなく、元の関手の等式として比較する。
使われ方：区間分割の合成則と語の遷移の合成則。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.SegmentRestriction
open CategoryTheory

variable {C : Type u} [Category.{v} C] {W : MorphismProperty C} {w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} {X Y : C}

/-- 大きい区間の中の小さい区間の各位置の埋め込み。 -/
def inclusion (p q l r : Fin (w.length + 1)) (hpl : p ≤ l) (hlr : l ≤ r) (hrq : r ≤ q) :
    Fin (r.val - l.val + 1) →o Fin (q.val - p.val + 1) where
  toFun k := ⟨l.val - p.val + k.val, by have := k.isLt; omega⟩
  monotone' i j hij := by
    change l.val - p.val + i.val ≤ l.val - p.val + j.val
    exact Nat.add_le_add_left hij _

/-- 区間の位置の二通りの回収は同じ元の頂点。 -/
lemma index_inclusion (p q l r : Fin (w.length + 1)) (hpl : p ≤ l) (hlr : l ≤ r)
    (hrq : r ≤ q) (k : Fin (r.val - l.val + 1)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Segment.index p q (hpl.trans (hlr.trans hrq)) (inclusion p q l r hpl hlr hrq k) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Segment.index l r hlr k := by
  apply Fin.ext
  dsimp [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Segment.index, inclusion]
  omega

/-- 同じ列番号による、元の向き付き射の移送。 -/
lemma arrow_heq (d : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Direction) (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W w X Y) {i j : Fin w.length}
    (hi : w.direction i = d) (hj : w.direction j = d) (hij : i = j) :
    HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DirectionCategory.arrow d S i hi) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DirectionCategory.arrow d S j hj) := by
  cases hij
  rfl

/-- 小さい区間の射列は、大きい区間の同じ元の射列の制限。 -/
lemma chain_restriction (d : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Direction) (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W w X Y)
    (p q l r : Fin (w.length + 1)) (hpl : p ≤ l) (hlr : l ≤ r) (hrq : r ≤ q)
    (hd : ∀ i : Fin w.length, p.val ≤ i.val → i.val < q.val → w.direction i = d) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Segment.chain d S l r hlr (fun i hi hi' => hd i (by omega) (by omega)) =
      (inclusion p q l r hpl hlr hrq).toFunctor ⋙
        _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Segment.chain d S p q (hpl.trans (hlr.trans hrq)) hd := by
  let hObj (k : Fin (r.val - l.val + 1)) :=
    congrArg (fun j => _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DirectionCategory.vertex d (S.vertex j))
      (index_inclusion p q l r hpl hlr hrq k).symm
  apply ComposableArrows.ext hObj
  intro k hk
  apply (conj_eqToHom_iff_heq _ _ (hObj ⟨k, by omega⟩) (hObj ⟨k + 1, by omega⟩)).2
  change HEq ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Segment.chain d S l r hlr _).map' k (k + 1) (by omega) (by omega))
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Segment.chain d S p q _ hd).map' (l.val - p.val + k) (l.val - p.val + k + 1)
      (by omega) (by omega))
  dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Segment.chain]
  rw [ComposableArrows.mkOfObjOfMapSucc_map_succ _ _ k hk,
    ComposableArrows.mkOfObjOfMapSucc_map_succ _ _ (l.val - p.val + k) (by omega)]
  apply arrow_heq
  apply Fin.ext
  dsimp
  omega

/-- 元の頂点の、大きい区間の中での位置。 -/
def coordinate (p q i : Fin (w.length + 1)) (hpi : p ≤ i) (hiq : i ≤ q) :
    Fin (q.val - p.val + 1) := ⟨i.val - p.val, by omega⟩

lemma index_coordinate (p q i : Fin (w.length + 1)) (hpi : p ≤ i) (hiq : i ≤ q) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Segment.index p q (hpi.trans hiq) (coordinate p q i hpi hiq) = i := by
  apply Fin.ext
  dsimp [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Segment.index, coordinate]
  omega

lemma coordinate_monotone (p q i j : Fin (w.length + 1)) (hpi : p ≤ i) (hij : i ≤ j)
    (hjq : j ≤ q) :
    coordinate p q i hpi (hij.trans hjq) ≤ coordinate p q j (hpi.trans hij) hjq := by
  change i.val - p.val ≤ j.val - p.val
  omega

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.SegmentRestriction
