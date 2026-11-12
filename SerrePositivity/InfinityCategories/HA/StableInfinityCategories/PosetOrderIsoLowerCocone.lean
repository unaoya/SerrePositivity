module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.PosetNestedLowerCocone

/-!
概要：順序同型に沿う下方添字と同じ実余錐の厳密比較。
方針：同じ実図式の native 余錐・頂点・二辺を保持して比較する。
規約：一般安定性を先取りしない。使われ方：HA 1.4.2.15 の外側の面。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories
variable {P Q : Type u} [PartialOrder P] [PartialOrder Q]

def posetOrderIsoLowerOrderIso (e : P ≃o Q) (T : Q → Prop) (c : P) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.PosetSubtypeLowerIndex (fun p ↦ T (e p)) c ≃o _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.PosetSubtypeLowerIndex T (e c) where
  toFun p := ⟨e p.val, p.property.1, e.map_rel_iff'.mpr p.property.2⟩
  invFun p := ⟨e.symm p.val, by simpa only [e.apply_symm_apply] using p.property.1,
    by
      have h : e.toEquiv.symm p.val ≤ e.toEquiv.symm (e.toEquiv c) :=
        e.symm.map_rel_iff'.mpr p.property.2
      rw [e.toEquiv.symm_apply_apply] at h
      exact h⟩
  left_inv p := Subtype.ext (e.left_inv p.val)
  right_inv p := Subtype.ext (e.right_inv p.val)
  map_rel_iff' := e.map_rel_iff'

def posetOrderIsoLowerNerveIso (e : P ≃o Q) (T : Q → Prop) (c : P) :
    nerve (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.PosetSubtypeLowerIndex (fun p ↦ T (e p)) c) ≅
      nerve (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.PosetSubtypeLowerIndex T (e c)) :=
  PartOrd.nerveFunctor.mapIso (PartOrd.Iso.mk
    (α := PartOrd.of (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.PosetSubtypeLowerIndex (fun p ↦ T (e p)) c))
    (β := PartOrd.of (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.PosetSubtypeLowerIndex T (e c))) (posetOrderIsoLowerOrderIso e T c))

def posetOrderIsoFunctor (e : P ≃o Q) : P ⥤ Q :=
  (⟨e, fun _ _ h ↦ e.map_rel_iff'.mpr h⟩ : P →o Q).toFunctor

lemma posetOrderIsoLowerCocone_val (e : P ≃o Q) (T : Q → Prop) (c : P) :
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetSubtypeLowerCocone (fun p ↦ T (e p)) c).val ≫
      nerveMap (posetOrderIsoFunctor e) =
      ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetSubtypeLowerCocone T (e c)).restrict (posetOrderIsoLowerNerveIso e T c).hom).val := by
  let a := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone (nerveMap (posetOrderIsoFunctor e))
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetSubtypeLowerCocone (fun p ↦ T (e p)) c)
  let b := (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetSubtypeLowerCocone T (e c)).restrict (posetOrderIsoLowerNerveIso e T c).hom
  have hbase : (posetOrderIsoLowerNerveIso e T c).hom ≫
      (nerveMap (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetSubtypeLowerProjection T (e c)) ≫ nerveMap (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetSubtypeInclusion T)) =
      (nerveMap (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetSubtypeLowerProjection (fun p ↦ T (e p)) c) ≫
        nerveMap (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetSubtypeInclusion (fun p ↦ T (e p)))) ≫
          nerveMap (posetOrderIsoFunctor e) := by
    apply _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.thinNerveHom_ext_of_vertices
    intro v
    rfl
  let b' : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone
      ((nerveMap (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetSubtypeLowerProjection (fun p ↦ T (e p)) c) ≫
        nerveMap (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetSubtypeInclusion (fun p ↦ T (e p)))) ≫
          nerveMap (posetOrderIsoFunctor e)) := ⟨b.val, b.property.trans hbase⟩
  change a.val = b'.val
  apply _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.thinNerveCocone_val_eq_of_vertex
  change a.vertex = b.vertex
  dsimp only [a, b]
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.mapJoinCocone_vertex, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetSubtypeLowerCocone_vertex,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone.vertex_restrict, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetSubtypeLowerCocone_vertex]
  rfl

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
