module
public import SerrePositivity.InfinityCategories.Stable.PosetSubtypeLowerCocone
public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.CoconeTransformationPointPost

/-!
概要：入れ子の順序部分型の下方添字と同じ実余錐の比較。
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

def posetNestedLowerOrderIso (T U : P → Prop) (hTU : ∀ p, T p → U p)
    (c : {p : P // U p}) :
    PosetSubtypeLowerIndex (fun p : {p : P // U p} ↦ T p.val) c ≃o
      PosetSubtypeLowerIndex T c.val where
  toFun p := ⟨p.val.val, p.property.1, p.property.2⟩
  invFun p := ⟨⟨p.val, hTU _ p.property.1⟩, p.property.1, p.property.2⟩
  left_inv _ := Subtype.ext (Subtype.ext rfl)
  right_inv _ := Subtype.ext rfl
  map_rel_iff' := Iff.rfl

def posetNestedLowerNerveIso (T U : P → Prop) (hTU : ∀ p, T p → U p)
    (c : {p : P // U p}) :
    nerve (PosetSubtypeLowerIndex (fun p : {p : P // U p} ↦ T p.val) c) ≅
      nerve (PosetSubtypeLowerIndex T c.val) :=
  PartOrd.nerveFunctor.mapIso (PartOrd.Iso.mk
    (α := PartOrd.of (PosetSubtypeLowerIndex (fun p : {p : P // U p} ↦ T p.val) c))
    (β := PartOrd.of (PosetSubtypeLowerIndex T c.val)) (posetNestedLowerOrderIso T U hTU c))

lemma posetNestedLowerCocone_val (T U : P → Prop) (hTU : ∀ p, T p → U p)
    (c : {p : P // U p}) :
    (posetSubtypeLowerCocone (fun p : {p : P // U p} ↦ T p.val) c).val ≫
      nerveMap (posetSubtypeInclusion U) =
      ((posetSubtypeLowerCocone T c.val).restrict
        (posetNestedLowerNerveIso T U hTU c).hom).val := by
  let a := mapJoinCocone (nerveMap (posetSubtypeInclusion U))
    (posetSubtypeLowerCocone (fun p : {p : P // U p} ↦ T p.val) c)
  let b := (posetSubtypeLowerCocone T c.val).restrict
    (posetNestedLowerNerveIso T U hTU c).hom
  have hbase : (posetNestedLowerNerveIso T U hTU c).hom ≫
      (nerveMap (posetSubtypeLowerProjection T c.val) ≫
        nerveMap (posetSubtypeInclusion T)) =
      (nerveMap (posetSubtypeLowerProjection (fun p : {p : P // U p} ↦ T p.val) c) ≫
        nerveMap (posetSubtypeInclusion (fun p : {p : P // U p} ↦ T p.val))) ≫
          nerveMap (posetSubtypeInclusion U) := by
    apply thinNerveHom_ext_of_vertices
    intro v
    rfl
  let b' : JoinCocone
      ((nerveMap (posetSubtypeLowerProjection (fun p : {p : P // U p} ↦ T p.val) c) ≫
        nerveMap (posetSubtypeInclusion (fun p : {p : P // U p} ↦ T p.val))) ≫
          nerveMap (posetSubtypeInclusion U)) := ⟨b.val, b.property.trans hbase⟩
  change a.val = b'.val
  apply thinNerveCocone_val_eq_of_vertex
  change (mapJoinCocone (nerveMap (posetSubtypeInclusion U))
    (posetSubtypeLowerCocone (fun p : {p : P // U p} ↦ T p.val) c)).vertex = b.vertex
  rw [F2.Ind.mapJoinCocone_vertex, posetSubtypeLowerCocone_vertex]
  dsimp only [b]
  rw [JoinCocone.vertex_restrict, posetSubtypeLowerCocone_vertex]
  rfl

end SerrePositivity.InfinityCategories
