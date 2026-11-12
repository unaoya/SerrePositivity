module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.PosetSubtypeLowerCocone
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.CoconeTransformationPointPost

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
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories
variable {P : Type u} [PartialOrder P]

def posetNestedLowerOrderIso (T U : P → Prop) (hTU : ∀ p, T p → U p)
    (c : {p : P // U p}) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.PosetSubtypeLowerIndex (fun p : {p : P // U p} ↦ T p.val) c ≃o
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.PosetSubtypeLowerIndex T c.val where
  toFun p := ⟨p.val.val, p.property.1, p.property.2⟩
  invFun p := ⟨⟨p.val, hTU _ p.property.1⟩, p.property.1, p.property.2⟩
  left_inv _ := Subtype.ext (Subtype.ext rfl)
  right_inv _ := Subtype.ext rfl
  map_rel_iff' := Iff.rfl

def posetNestedLowerNerveIso (T U : P → Prop) (hTU : ∀ p, T p → U p)
    (c : {p : P // U p}) :
    nerve (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.PosetSubtypeLowerIndex (fun p : {p : P // U p} ↦ T p.val) c) ≅
      nerve (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.PosetSubtypeLowerIndex T c.val) :=
  PartOrd.nerveFunctor.mapIso (PartOrd.Iso.mk
    (α := PartOrd.of (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.PosetSubtypeLowerIndex (fun p : {p : P // U p} ↦ T p.val) c))
    (β := PartOrd.of (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.PosetSubtypeLowerIndex T c.val)) (posetNestedLowerOrderIso T U hTU c))

lemma posetNestedLowerCocone_val (T U : P → Prop) (hTU : ∀ p, T p → U p)
    (c : {p : P // U p}) :
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetSubtypeLowerCocone (fun p : {p : P // U p} ↦ T p.val) c).val ≫
      nerveMap (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetSubtypeInclusion U) =
      ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetSubtypeLowerCocone T c.val).restrict
        (posetNestedLowerNerveIso T U hTU c).hom).val := by
  let a := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone (nerveMap (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetSubtypeInclusion U))
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetSubtypeLowerCocone (fun p : {p : P // U p} ↦ T p.val) c)
  let b := (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetSubtypeLowerCocone T c.val).restrict
    (posetNestedLowerNerveIso T U hTU c).hom
  have hbase : (posetNestedLowerNerveIso T U hTU c).hom ≫
      (nerveMap (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetSubtypeLowerProjection T c.val) ≫
        nerveMap (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetSubtypeInclusion T)) =
      (nerveMap (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetSubtypeLowerProjection (fun p : {p : P // U p} ↦ T p.val) c) ≫
        nerveMap (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetSubtypeInclusion (fun p : {p : P // U p} ↦ T p.val))) ≫
          nerveMap (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetSubtypeInclusion U) := by
    apply _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.thinNerveHom_ext_of_vertices
    intro v
    rfl
  let b' : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone
      ((nerveMap (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetSubtypeLowerProjection (fun p : {p : P // U p} ↦ T p.val) c) ≫
        nerveMap (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetSubtypeInclusion (fun p : {p : P // U p} ↦ T p.val))) ≫
          nerveMap (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetSubtypeInclusion U)) := ⟨b.val, b.property.trans hbase⟩
  change a.val = b'.val
  apply _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.thinNerveCocone_val_eq_of_vertex
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone (nerveMap (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetSubtypeInclusion U))
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetSubtypeLowerCocone (fun p : {p : P // U p} ↦ T p.val) c)).vertex = b.vertex
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.mapJoinCocone_vertex, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetSubtypeLowerCocone_vertex]
  dsimp only [b]
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone.vertex_restrict, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetSubtypeLowerCocone_vertex]
  rfl

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
