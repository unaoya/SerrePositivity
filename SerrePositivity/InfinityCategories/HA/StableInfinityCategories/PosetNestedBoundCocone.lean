module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.PosetNestedLowerCocone

/-!
概要：指定上界の実余錐を元の下方余錐へ厳密に戻す。
方針：同じ実図式の native 余錐と頂点を保持して比較する。
規約：一般安定性を先取りしない。使われ方：HA 1.4.2.15 の中央面。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories
variable {P : Type u} [PartialOrder P]

def posetNestedBoundLowerOrderIso (T U : P → Prop) (hTU : ∀ p, T p → U p)
    (c : P) (hbound : ∀ p, T p → p ≤ c) :
    {p : {p : P // U p} // T p.val} ≃o _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.PosetSubtypeLowerIndex T c where
  toFun p := ⟨p.val.val, p.property, hbound _ p.property⟩
  invFun p := ⟨⟨p.val, hTU _ p.property.1⟩, p.property.1⟩
  left_inv _ := Subtype.ext (Subtype.ext rfl)
  right_inv _ := Subtype.ext rfl
  map_rel_iff' := Iff.rfl

def posetNestedBoundLowerNerveIso (T U : P → Prop) (hTU : ∀ p, T p → U p)
    (c : P) (hbound : ∀ p, T p → p ≤ c) :
    nerve {p : {p : P // U p} // T p.val} ≅ nerve (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.PosetSubtypeLowerIndex T c) :=
  PartOrd.nerveFunctor.mapIso (PartOrd.Iso.mk
    (α := PartOrd.of {p : {p : P // U p} // T p.val})
    (β := PartOrd.of (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.PosetSubtypeLowerIndex T c))
    (posetNestedBoundLowerOrderIso T U hTU c hbound))

lemma posetNestedBoundCocone_restrict_val (T U : P → Prop) (hTU : ∀ p, T p → U p)
    (c : P) (hbound : ∀ p, T p → p ≤ c)
    (d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (nerveMap (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetSubtypeInclusion U))) (hd : d.vertex = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex c) :
    (d.restrict (nerveMap
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetSubtypeInclusion (fun p : {p : P // U p} ↦ T p.val)))).val =
      ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetSubtypeLowerCocone T c).restrict
        (posetNestedBoundLowerNerveIso T U hTU c hbound).hom).val := by
  let b := (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetSubtypeLowerCocone T c).restrict
    (posetNestedBoundLowerNerveIso T U hTU c hbound).hom
  have hbase : (posetNestedBoundLowerNerveIso T U hTU c hbound).hom ≫
      (nerveMap (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetSubtypeLowerProjection T c) ≫ nerveMap (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetSubtypeInclusion T)) =
      nerveMap (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetSubtypeInclusion (fun p : {p : P // U p} ↦ T p.val)) ≫
        nerveMap (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetSubtypeInclusion U) := by
    apply _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.thinNerveHom_ext_of_vertices
    intro v
    rfl
  let b' : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone
      (nerveMap (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetSubtypeInclusion (fun p : {p : P // U p} ↦ T p.val)) ≫
        nerveMap (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetSubtypeInclusion U)) := ⟨b.val, b.property.trans hbase⟩
  change (d.restrict _).val = b'.val
  apply _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.thinNerveCocone_val_eq_of_vertex
  change (d.restrict _).vertex = b.vertex
  dsimp only [b]
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone.vertex_restrict, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone.vertex_restrict,
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetSubtypeLowerCocone_vertex, hd]

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
