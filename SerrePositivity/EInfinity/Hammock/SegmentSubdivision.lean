module

public import SerrePositivity.EInfinity.Hammock.SegmentParentComparison

/-!
# 同方向区間の分割と元の合成

概要：一つの同方向区間を二つに分けた合成は、元の区間の合成と等しい。
方針：三つの射を同じ大区間の射列の射と比較し、その関手性を使う。
規約：元の圏または反対圏での等式であり、弱同値性は不要。
使われ方：語の遷移関手の合成の照合。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.EInfinity.Hammock.Segment
open CategoryTheory

variable {C : Type u} [Category.{v} C] {W : MorphismProperty C} {w : Word} {X Y : C}

/-- 二つの隣接する同方向区間の合成は、同じ元の全区間の合成。 -/
lemma map_comp (d : Direction) (S : Zigzag W w X Y)
    (p q r : Fin (w.length + 1)) (hpq : p ≤ q) (hqr : q ≤ r)
    (hd : ∀ i : Fin w.length, p.val ≤ i.val → i.val < r.val → w.direction i = d) :
    map d S p r (hpq.trans hqr) hd =
      map d S p q hpq (fun i hi hi' => hd i hi (by omega)) ≫
        map d S q r hqr (fun i hi hi' => hd i (by omega) hi') := by
  let F := chain d S p r (hpq.trans hqr) hd
  let ip := coordinate p r p le_rfl (hpq.trans hqr)
  let iq := coordinate p r q hpq hqr
  let ir := coordinate p r r (hpq.trans hqr) le_rfl
  let f : ip ⟶ iq := homOfLE (coordinate_monotone p r p q le_rfl hpq hqr)
  let g : iq ⟶ ir := homOfLE (coordinate_monotone p r q r hpq hqr le_rfl)
  have hpr := map_parent_heq d S p r p r le_rfl (hpq.trans hqr) le_rfl hd
  have hpq' := map_parent_heq d S p r p q le_rfl hpq hqr hd
  have hqr' := map_parent_heq d S p r q r hpq hqr le_rfl hd
  have hprod := heq_comp
    (chain_obj_coordinate d S p r p le_rfl (hpq.trans hqr) hd).symm
    (chain_obj_coordinate d S p r q hpq hqr hd).symm
    (chain_obj_coordinate d S p r r (hpq.trans hqr) le_rfl hd).symm hpq' hqr'
  have hf : F.map (homOfLE (coordinate_monotone p r p r le_rfl (hpq.trans hqr) le_rfl)) =
      F.map f ≫ F.map g := F.map_comp f g
  exact eq_of_heq (hpr.trans ((heq_of_eq hf).trans hprod.symm))

end SerrePositivity.EInfinity.Hammock.Segment
