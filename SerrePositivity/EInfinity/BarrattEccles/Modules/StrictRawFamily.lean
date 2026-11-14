module

public import SerrePositivity.EInfinity.BarrattEccles.Modules.StrictRawCoherence
public import Mathlib.CategoryTheory.Bicategory.Grothendieck

/-!
# 厳密 BE 加群の局所化前の全圏

概要：HA §4.2.3 の元の dg 加群を、変わる厳密底上の一つの圏に組み立てる。
方針：同じ制限の擬関手と元の比較から反変 Grothendieck 構成を使う。
規約：native CAlg 上の局所化・cocartesian 性は別に検証する。
使われ方：BE の全加群族の相対局所化への入力。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory CategoryTheory.Bicategory
open scoped CategoryTheory.Bicategory
variable (A : Type u) [CommRing A]

/-- 概要：同じ dg 加群制限の反変な擬関手（HA §4.2.3）。
方針：元の比較の唯一点での評価から全ての coherence を照合する。
規約：指定された同じ制限。使われ方：局所化前の全加群圏。 -/
def strictRawModuleRestrictionPseudofunctor :
    LocallyDiscrete ((operad A).Algebraᵒᵖ) ⥤ᵖ Cat.{u, u+1} where
  obj X := Cat.of (strictRawModuleCategory A X.as.unop)
  map f := (strictRawModuleRestrict f.as.unop).toCatHom
  map₂ {X Y} {f g} η := eqToHom (congrArg (fun f : X ⟶ Y => (strictRawModuleRestrict f.as.unop).toCatHom)
    (LocallyDiscrete.eq_of_hom η))
  map₂_id := by intros; rfl
  map₂_comp := by intros; simp only [eqToHom_trans]
  mapId X := Cat.Hom.isoMk (strictRawModuleRestrict_idIso X.as.unop)
  mapComp f g := Cat.Hom.isoMk (strictRawModuleRestrict_compIso g.as.unop f.as.unop).symm
  map₂_whisker_left := by
    intro X Y Z f g h η
    obtain rfl := LocallyDiscrete.eq_of_hom η
    have hη : η = 𝟙 g := Subsingleton.elim _ _
    subst η
    simp only [eqToHom_refl, whiskerLeft_id, Category.id_comp]
    exact (Cat.Hom.isoMk (strictRawModuleRestrict_compIso g.as.unop f.as.unop)).inv_hom_id.symm
  map₂_whisker_right := by
    intro X Y Z f g η h
    obtain rfl := LocallyDiscrete.eq_of_hom η
    have hη : η = 𝟙 f := Subsingleton.elim _ _
    subst η
    simp only [eqToHom_refl, id_whiskerRight, Category.id_comp]
    exact (Cat.Hom.isoMk (strictRawModuleRestrict_compIso h.as.unop f.as.unop)).inv_hom_id.symm
  map₂_associator := by
    intro W X Y Z f g h
    apply Cat.Hom₂.ext
    apply NatTrans.ext
    funext M
    apply strictRawModuleHom_ext
    simp only [Cat.Hom.isoMk, NatTrans.toCatHom₂, Functor.toCatHom,
      Iso.symm_hom, Iso.symm_inv, Cat.Hom₂.comp_app, Cat.eqToHom_app, Cat.whiskerLeft_app,
      Cat.whiskerRight_app, Cat.associator_hom_app, eqToHom_map, CategoryTheory.Functor.map_comp,
      strictRawModuleRestrict_compIso_eval, strictRawModuleRestrict_compIso_inv_eval,
      strictRawModuleRestrict_eval,
      Category.comp_id]
    all_goals rfl
  map₂_left_unitor := by
    intro X Y f
    apply Cat.Hom₂.ext
    apply NatTrans.ext
    funext M
    apply strictRawModuleHom_ext
    simp only [Cat.Hom.isoMk, NatTrans.toCatHom₂, Functor.toCatHom,
      Iso.symm_hom, Iso.symm_inv, Cat.Hom₂.comp_app, Cat.eqToHom_app, Cat.whiskerRight_app,
      Cat.leftUnitor_hom_app, eqToHom_map, CategoryTheory.Functor.map_comp,
      strictRawModuleRestrict_compIso_inv_eval, strictRawModuleRestrict_idIso_eval,
      strictRawModuleRestrict_eval,
      Category.comp_id]
    all_goals rfl
  map₂_right_unitor := by
    intro X Y f
    apply Cat.Hom₂.ext
    apply NatTrans.ext
    funext M
    apply strictRawModuleHom_ext
    simp only [Cat.Hom.isoMk, NatTrans.toCatHom₂, Functor.toCatHom,
      Iso.symm_hom, Iso.symm_inv, Cat.Hom₂.comp_app, Cat.eqToHom_app, Cat.whiskerLeft_app,
      Cat.rightUnitor_hom_app, eqToHom_map, CategoryTheory.Functor.map_comp,
      strictRawModuleRestrict_compIso_inv_eval, strictRawModuleRestrict_idIso_eval,
      Category.comp_id]
    all_goals rfl

/-- 概要：変わる厳密 BE 底上の全 dg 加群の通常の圏（HA §4.2.3）。
方針：同じ反変擬関手の Grothendieck 構成。
規約：射は底の射とその制限への元の加群射。使われ方：相対局所化の全圏。 -/
abbrev strictRawModuleTotal := Pseudofunctor.CoGrothendieck
  (strictRawModuleRestrictionPseudofunctor A)

/-- 概要：元の全加群圏から同じ厳密 BE 代数への射影（HA §4.2.3）。
方針：元の Grothendieck 射影を使う。
規約：底の代数と射を保持。使われ方：native CAlg 上の族への入力。 -/
def strictRawModuleProjection : strictRawModuleTotal A ⥤ (operad A).Algebra :=
  Pseudofunctor.CoGrothendieck.forget (strictRawModuleRestrictionPseudofunctor A)

end SerrePositivity.EInfinity.BarrattEccles
