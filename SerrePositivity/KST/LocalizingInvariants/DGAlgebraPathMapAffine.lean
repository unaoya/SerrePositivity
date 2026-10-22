module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPathMapLaws

/-!
概要：元の代数射の underlying 射の affine 等式は、経路射の underlying 射にも移る。
方針：両端と元の比較 cochain の三成分の一意性を使う。
規約：元の四つの射は実代数射。使われ方：相対平方零経路の厳密な相殺。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Preadditive CochainComplex HomComplex
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.Path
variable (R : Type u) [CommRing R] {A B : Mon (Complex R)} (s t u v : A ⟶ B)
  (h : v.hom = s.hom - t.hom + u.hom)

include h in
lemma map_affine : (map R v).hom = (map R s).hom - (map R t).hom + (map R u).hom := by
  apply chain_ext R B
  · change mapHom R v ≫ (source R B).hom =
      (mapHom R s - mapHom R t + mapHom R u) ≫ (source R B).hom
    rw [add_comp, sub_comp, mapHom_source, mapHom_source, mapHom_source, mapHom_source,
      h, comp_add, comp_sub]
  · change mapHom R v ≫ (target R B).hom =
      (mapHom R s - mapHom R t + mapHom R u) ≫ (target R B).hom
    rw [add_comp, sub_comp, mapHom_target, mapHom_target, mapHom_target, mapHom_target,
      h, comp_add, comp_sub]
  · change (Cochain.ofHom (mapHom R v)).comp (primitive R B) _ =
      (Cochain.ofHom (mapHom R s - mapHom R t + mapHom R u)).comp (primitive R B) _
    rw [Cochain.ofHom_add, Cochain.ofHom_sub, Cochain.add_comp, Cochain.sub_comp,
      mapHom_primitive, mapHom_primitive, mapHom_primitive, mapHom_primitive,
      h, Cochain.ofHom_add, Cochain.ofHom_sub, Cochain.comp_add, Cochain.comp_sub]

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.Path
