module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.SegmentParentComparison

/-!
# 同方向区間の分割と元の合成

概要：一つの同方向区間を二つに分けた合成は、元の区間の合成と等しい。
方針：三つの射を同じ大区間の射列の射と比較し、その関手性を使う。
規約：元の圏または反対圏での等式であり、弱同値性は不要。
使われ方：語の遷移関手の合成の照合。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.SegmentSubdivision
open CategoryTheory

variable {C : Type u} [Category.{v} C] {W : MorphismProperty C} {w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} {X Y : C}

/-- 二つの隣接する同方向区間の合成は、同じ元の全区間の合成。 -/
lemma map_comp (d : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Direction) (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W w X Y)
    (p q r : Fin (w.length + 1)) (hpq : p ≤ q) (hqr : q ≤ r)
    (hd : ∀ i : Fin w.length, p.val ≤ i.val → i.val < r.val → w.direction i = d) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Segment.map d S p r (hpq.trans hqr) hd =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Segment.map d S p q hpq (fun i hi hi' => hd i hi (by omega)) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Segment.map d S q r hqr (fun i hi hi' => hd i (by omega) hi') := by
  let F := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Segment.chain d S p r (hpq.trans hqr) hd
  let ip := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.SegmentRestriction.coordinate p r p le_rfl (hpq.trans hqr)
  let iq := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.SegmentRestriction.coordinate p r q hpq hqr
  let ir := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.SegmentRestriction.coordinate p r r (hpq.trans hqr) le_rfl
  let f : ip ⟶ iq := homOfLE (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.SegmentRestriction.coordinate_monotone p r p q le_rfl hpq hqr)
  let g : iq ⟶ ir := homOfLE (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.SegmentRestriction.coordinate_monotone p r q r hpq hqr le_rfl)
  have hpr := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.map_parent_heq d S p r p r le_rfl (hpq.trans hqr) le_rfl hd
  have hpq' := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.map_parent_heq d S p r p q le_rfl hpq hqr hd
  have hqr' := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.map_parent_heq d S p r q r hpq hqr le_rfl hd
  have hprod := heq_comp
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.chain_obj_coordinate d S p r p le_rfl (hpq.trans hqr) hd).symm
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.chain_obj_coordinate d S p r q hpq hqr hd).symm
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.chain_obj_coordinate d S p r r (hpq.trans hqr) le_rfl hd).symm hpq' hqr'
  have hf : F.map (homOfLE (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.SegmentRestriction.coordinate_monotone p r p r le_rfl (hpq.trans hqr) le_rfl)) =
      F.map f ≫ F.map g := F.map_comp f g
  exact eq_of_heq (hpr.trans ((heq_of_eq hf).trans hprod.symm))

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.SegmentSubdivision
