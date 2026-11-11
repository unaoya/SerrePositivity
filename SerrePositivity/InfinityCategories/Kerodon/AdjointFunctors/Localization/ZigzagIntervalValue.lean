module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValuePath
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.SegmentSubdivision
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.SegmentAdjacent
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.SegmentUnits

/-!
# 元の同方向の区間の反転関手による値

概要：同方向の全区間の合成を関手で評価し、後ろ向きならその像を反転する。
方針：元の区間の分割・隣接列・空区間の式を合成と逆射の一意性で移す。
規約：元の区間と元の弱同値の合成を保持する。
使われ方：元の WordAction の全 fiber の圧縮への値の不変性。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v u' v'
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory Opposite

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {W : MorphismProperty C} [W.IsMultiplicative] (L : C ⥤ D) (hL : W.IsInvertedBy L)
  {w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} {X Y : C}

def intervalBackwardIso (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W w X Y) (p q : Fin (w.length + 1)) (hpq : p ≤ q)
    (hd : ∀ i : Fin w.length, p.val ≤ i.val → i.val < q.val → w.direction i = .backward) :
    L.obj (S.vertex q) ≅ L.obj (S.vertex p) := by
  have : IsIso (L.map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Segment.map .backward S p q hpq hd).unop) :=
    hL _ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Segment.map_allowed .backward S p q hpq hd)
  exact asIso (L.map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Segment.map .backward S p q hpq hd).unop)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.Value.intervalBackwardIso export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (intervalBackwardIso)


def intervalValue (d : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Direction) (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W w X Y)
    (p q : Fin (w.length + 1)) (hpq : p ≤ q)
    (hd : ∀ i : Fin w.length, p.val ≤ i.val → i.val < q.val → w.direction i = d) :
    L.obj (S.vertex p) ⟶ L.obj (S.vertex q) := by
  cases d with
  | forward => exact L.map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Segment.map .forward S p q hpq hd)
  | backward => exact (intervalBackwardIso L hL S p q hpq hd).inv

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.Value.intervalValue export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (intervalValue)


lemma intervalValue_refl (d : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Direction) (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W w X Y) (p : Fin (w.length + 1))
    (hd : ∀ i : Fin w.length, p.val ≤ i.val → i.val < p.val → w.direction i = d) :
    intervalValue L hL d S p p le_rfl hd = 𝟙 _ := by
  cases d with
  | forward =>
    change L.map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Segment.map .forward S p p le_rfl hd) = 𝟙 _
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.map_refl, L.map_id]
  | backward =>
    change (intervalBackwardIso L hL S p p le_rfl hd).inv = 𝟙 _
    have hh : (intervalBackwardIso L hL S p p le_rfl hd).hom = 𝟙 _ := by
      change L.map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Segment.map .backward S p p le_rfl hd).unop = 𝟙 _
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.map_refl]
      exact L.map_id _
    apply (cancel_mono (intervalBackwardIso L hL S p p le_rfl hd).hom).1
    rw [Iso.inv_hom_id, Category.id_comp, hh]

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.Value.intervalValue_refl export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (intervalValue_refl)


lemma intervalValue_comp (d : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Direction) (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W w X Y)
    (p q r : Fin (w.length + 1)) (hpq : p ≤ q) (hqr : q ≤ r)
    (hd : ∀ i : Fin w.length, p.val ≤ i.val → i.val < r.val → w.direction i = d) :
    intervalValue L hL d S p r (hpq.trans hqr) hd =
      intervalValue L hL d S p q hpq (fun i hi hi' => hd i hi (by omega)) ≫
        intervalValue L hL d S q r hqr (fun i hi hi' => hd i (by omega) hi') := by
  cases d with
  | forward =>
    change L.map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Segment.map .forward S p r _ hd) =
      L.map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Segment.map .forward S p q _ _) ≫ L.map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Segment.map .forward S q r _ _)
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.SegmentSubdivision.map_comp, L.map_comp]
  | backward =>
    have hh : (intervalBackwardIso L hL S p r (hpq.trans hqr) hd).hom =
        (intervalBackwardIso L hL S q r hqr (fun i hi hi' => hd i (by omega) hi')).hom ≫
        (intervalBackwardIso L hL S p q hpq (fun i hi hi' => hd i hi (by omega))).hom := by
      change L.map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Segment.map .backward S p r _ hd).unop =
        L.map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Segment.map .backward S q r _ _).unop ≫
          L.map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Segment.map .backward S p q _ _).unop
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.SegmentSubdivision.map_comp, unop_comp, L.map_comp]
    have he : intervalBackwardIso L hL S p r (hpq.trans hqr) hd =
        intervalBackwardIso L hL S q r hqr (fun i hi hi' => hd i (by omega) hi') ≪≫
          intervalBackwardIso L hL S p q hpq (fun i hi hi' => hd i hi (by omega)) := by
      apply Iso.ext
      exact hh
    exact congrArg Iso.inv he

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.Value.intervalValue_comp export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (intervalValue_comp)


lemma intervalValue_adjacent (d : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Direction) (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W w X Y) (i : Fin w.length)
    (hi : w.direction i = d) :
    intervalValue L hL d S i.castSucc i.succ (Fin.castSucc_le_succ i)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.adjacent_direction d i hi) = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValuePath.edge L hL S i := by
  cases d with
  | forward =>
    change L.map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Segment.map .forward S i.castSucc i.succ _ _) = _
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValuePath.edge_forward L hL S i hi, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.map_adjacent]
  | backward =>
    have hh : intervalBackwardIso L hL S i.castSucc i.succ (Fin.castSucc_le_succ i)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.adjacent_direction .backward i hi) = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValuePath.backwardIso L hL S i hi := by
      apply Iso.ext
      change L.map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Segment.map .backward S i.castSucc i.succ _ _).unop =
        L.map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DirectionCategory.arrow .backward S i hi).unop
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.map_adjacent]
    change (intervalBackwardIso L hL S i.castSucc i.succ _ _).inv = _
    rw [hh, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValuePath.edge_backward L hL S i hi]

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.Value.intervalValue_adjacent export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (intervalValue_adjacent)


end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
