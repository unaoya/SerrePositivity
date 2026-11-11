module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.SegmentSubdivision
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.SegmentAdjacent

/-!
# 元の forward 区間の指定性と一列の前後での分割

概要：全列が指定された forward 区間の合成の指定性と、内部一列での三分割を証明する。
方針：元の射列の合成と二度の区間分割を使う。
規約：元の端点移送・元の射を保持する。空の前後の区間も許す。
使われ方：語の圧縮による最初の非指定切断の比較。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory

variable {C : Type u} [Category.{v} C] {W : MorphismProperty C} {w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} {X Y : C}
  (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W w X Y) (p q : Fin (w.length + 1)) (hpq : p ≤ q)
  (hd : ∀ i : Fin w.length, p.val ≤ i.val → i.val < q.val → w.direction i = .forward)

lemma forward_map_mem (V : MorphismProperty C) [V.IsMultiplicative]
    (hV : ∀ i : Fin w.length, p.val ≤ i.val → i.val < q.val → V (S.arrow i)) :
    V (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Segment.map .forward S p q hpq hd) := by
  apply V.comp_mem
  · exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Segment.eqToHom_mem _
  · apply V.comp_mem
    · apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Segment.chain_map_mem V
      intro k hk
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Segment.chain, ComposableArrows.mkOfObjOfMapSucc_map_succ _ _ k hk]
      change V (eqToHom _ ≫ S.arrow _ ≫ eqToHom _)
      apply (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DirectionCategory.transport_mem _ _ _).2
      apply hV
      · change p.val ≤ p.val + k
        omega
      · change p.val + k < q.val
        omega
    · exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Segment.eqToHom_mem _

lemma forward_map_split_column (i : Fin w.length)
    (hp : p.val ≤ i.val) (hq : i.val < q.val) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Segment.map .forward S p q hpq hd =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Segment.map .forward S p i.castSucc (by change p.val ≤ i.val; exact hp)
        (fun j hj hj' => hd j hj (by change j.val < i.val at hj'; omega)) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DirectionCategory.arrow .forward S i (hd i hp hq) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Segment.map .forward S i.succ q (by change i.val + 1 ≤ q.val; omega)
        (fun j hj hj' => hd j (by change i.val + 1 ≤ j.val at hj; omega) hj') := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.SegmentSubdivision.map_comp .forward S p i.castSucc q (by exact hp) (by change i.val ≤ q.val; omega)]
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.SegmentSubdivision.map_comp .forward S i.castSucc i.succ q (Fin.castSucc_le_succ i)
    (by change i.val + 1 ≤ q.val; omega)]
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.map_adjacent .forward S i (hd i hp hq)]

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
