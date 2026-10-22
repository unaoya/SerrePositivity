module
public import SerrePositivity.InfinityCategories.Stable.PosetNestedLowerCocone

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
namespace SerrePositivity.InfinityCategories
variable {P : Type u} [PartialOrder P]

def posetNestedBoundLowerOrderIso (T U : P → Prop) (hTU : ∀ p, T p → U p)
    (c : P) (hbound : ∀ p, T p → p ≤ c) :
    {p : {p : P // U p} // T p.val} ≃o PosetSubtypeLowerIndex T c where
  toFun p := ⟨p.val.val, p.property, hbound _ p.property⟩
  invFun p := ⟨⟨p.val, hTU _ p.property.1⟩, p.property.1⟩
  left_inv _ := Subtype.ext (Subtype.ext rfl)
  right_inv _ := Subtype.ext rfl
  map_rel_iff' := Iff.rfl

def posetNestedBoundLowerNerveIso (T U : P → Prop) (hTU : ∀ p, T p → U p)
    (c : P) (hbound : ∀ p, T p → p ≤ c) :
    nerve {p : {p : P // U p} // T p.val} ≅ nerve (PosetSubtypeLowerIndex T c) :=
  PartOrd.nerveFunctor.mapIso (PartOrd.Iso.mk
    (α := PartOrd.of {p : {p : P // U p} // T p.val})
    (β := PartOrd.of (PosetSubtypeLowerIndex T c))
    (posetNestedBoundLowerOrderIso T U hTU c hbound))

lemma posetNestedBoundCocone_restrict_val (T U : P → Prop) (hTU : ∀ p, T p → U p)
    (c : P) (hbound : ∀ p, T p → p ≤ c)
    (d : JoinCocone (nerveMap (posetSubtypeInclusion U))) (hd : d.vertex = nerveVertex c) :
    (d.restrict (nerveMap
      (posetSubtypeInclusion (fun p : {p : P // U p} ↦ T p.val)))).val =
      ((posetSubtypeLowerCocone T c).restrict
        (posetNestedBoundLowerNerveIso T U hTU c hbound).hom).val := by
  let b := (posetSubtypeLowerCocone T c).restrict
    (posetNestedBoundLowerNerveIso T U hTU c hbound).hom
  have hbase : (posetNestedBoundLowerNerveIso T U hTU c hbound).hom ≫
      (nerveMap (posetSubtypeLowerProjection T c) ≫ nerveMap (posetSubtypeInclusion T)) =
      nerveMap (posetSubtypeInclusion (fun p : {p : P // U p} ↦ T p.val)) ≫
        nerveMap (posetSubtypeInclusion U) := by
    apply thinNerveHom_ext_of_vertices
    intro v
    rfl
  let b' : JoinCocone
      (nerveMap (posetSubtypeInclusion (fun p : {p : P // U p} ↦ T p.val)) ≫
        nerveMap (posetSubtypeInclusion U)) := ⟨b.val, b.property.trans hbase⟩
  change (d.restrict _).val = b'.val
  apply thinNerveCocone_val_eq_of_vertex
  change (d.restrict _).vertex = b.vertex
  dsimp only [b]
  rw [JoinCocone.vertex_restrict, JoinCocone.vertex_restrict,
    posetSubtypeLowerCocone_vertex, hd]

end SerrePositivity.InfinityCategories
