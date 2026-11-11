module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.SegmentRestriction

/-!
# 小区間の合成と同じ大区間の射の比較

概要：小区間の合成を、一つの大区間の合成可能射列の対応する射と照合。
方針：射列の制限の等式から全射の異種等式を得て、端点の移送を取り除く。
規約：比較先の二つの頂点は元の区間内の位置であり、別の置換を使わない。
使われ方：共通の射列の関手性による区間分割の合成則。

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

/-- 同じ全順序の射列では、二つの位置の等式が元の射の異種等式を与える。 -/
lemma fin_map_heq {D : Type*} [Category D] {n : ℕ} (F : ComposableArrows D n)
    {p q p' q' : Fin (n + 1)} (hp : p = p') (hq : q = q') (f : p ⟶ q) (g : p' ⟶ q') :
    HEq (F.map f) (F.map g) := by
  cases hp
  cases hq
  have h : f = g := Subsingleton.elim _ _
  cases h
  rfl

/-- 小区間の合成は、同じ大区間の射列の元の対応射と異種等しい。 -/
lemma map_parent_heq (d : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Direction) (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W w X Y)
    (p q l r : Fin (w.length + 1)) (hpl : p ≤ l) (hlr : l ≤ r) (hrq : r ≤ q)
    (hd : ∀ i : Fin w.length, p.val ≤ i.val → i.val < q.val → w.direction i = d) :
    HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Segment.map d S l r hlr (fun i hi hi' => hd i (by omega) (by omega)))
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Segment.chain d S p q (hpl.trans (hlr.trans hrq)) hd).map
        (homOfLE (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.SegmentRestriction.coordinate_monotone p q l r hpl hlr hrq))) := by
  change HEq (eqToHom _ ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Segment.chain d S l r hlr _).hom ≫ eqToHom _) _
  simp only [eqToHom_comp_heq_iff, comp_eqToHom_heq_iff]
  have h := Functor.hcongr_hom (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.SegmentRestriction.chain_restriction d S p q l r hpl hlr hrq hd)
    (homOfLE (show (0 : Fin (r.val - l.val + 1)) ≤ Fin.last _ from Fin.zero_le _))
  refine h.trans (fin_map_heq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Segment.chain d S p q _ hd) ?_ ?_ _ _)
  · apply Fin.ext
    dsimp [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.SegmentRestriction.inclusion, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.SegmentRestriction.coordinate]
  · apply Fin.ext
    dsimp [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.SegmentRestriction.inclusion, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.SegmentRestriction.coordinate]
    omega

/-- 大区間の位置で回収した頂点は、元の同じ頂点。 -/
lemma chain_obj_coordinate (d : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Direction) (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W w X Y)
    (p q i : Fin (w.length + 1)) (hpi : p ≤ i) (hiq : i ≤ q)
    (hd : ∀ j : Fin w.length, p.val ≤ j.val → j.val < q.val → w.direction j = d) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Segment.chain d S p q (hpi.trans hiq) hd).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.SegmentRestriction.coordinate p q i hpi hiq) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DirectionCategory.vertex d (S.vertex i) :=
  congrArg (fun j => _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DirectionCategory.vertex d (S.vertex j)) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.SegmentRestriction.index_coordinate p q i hpi hiq)

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
