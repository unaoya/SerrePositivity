module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.ExtensionComparison

/-! # Compatibility of degree restrictions with maps of attached diagrams -/

@[expose] public section
universe v u t v' u'
noncomputable section
open CategoryTheory HomotopicalAlgebra

namespace SerrePositivity.Reedy.BoundaryExtension
variable {J : Type u} [Category.{v} J] {inverse direct : MorphismProperty J}
  [inverse.IsMultiplicative] [direct.IsMultiplicative]
  {α : Type t} [LinearOrder α] [OrderBot α] [SuccOrder α] [WellFoundedLT α]
  {r : ReedyStructure inverse direct α} {j : J}
  {C : Type u'} [Category.{v'} C] {H K : Lower r (r.deg j) ⥤ C}
  {d : BoundaryExtension r j H} {e : BoundaryExtension r j K} {τ : H ⟶ K}

lemma Map.degreeRestriction_naturality (m : Map d e τ) (hinj : Function.Injective r.deg) :
    Functor.whiskerLeft (lowerToUpper r j)
        (Functor.whiskerLeft (degreeIndex r j hinj) m.toNatTrans) ≫
      (e.degreeRestrictionIso hinj).hom = (d.degreeRestrictionIso hinj).hom ≫ τ := by
  ext x
  simp only [degreeRestrictionIso, Iso.trans_hom, NatTrans.comp_app, Iso.symm_hom,
    Functor.associator_inv_app, Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, NatIso.ofComponents_hom_app, eqToIso, restrictionIso,
    Category.id_comp]
  have h := m.toNatTrans.naturality (eqToHom (degreeIndex_obj_lower r j x))
  change d.toFunctor.map (eqToHom (degreeIndex_obj_lower r j x)) ≫ τ.app x =
    m.toNatTrans.app ((degreeIndex r j hinj).obj ((lowerToUpper r j).obj x)) ≫
      e.toFunctor.map (eqToHom (degreeIndex_obj_lower r j x)) at h
  change m.toNatTrans.app ((degreeIndex r j hinj).obj ((lowerToUpper r j).obj x)) ≫
      (e.toFunctor.map (eqToHom (degreeIndex_obj_lower r j x)) ≫
        𝟙 (e.toFunctor.obj (some x))) =
    (d.toFunctor.map (eqToHom (degreeIndex_obj_lower r j x)) ≫
      𝟙 (d.toFunctor.obj (some x))) ≫ τ.app x
  rw [Category.comp_id, Category.comp_id]
  exact h.symm

variable (r j) in
lemma ofFunctor_restriction (F : J ⥤ C) (hinj : Function.Injective r.deg) :
    Functor.whiskerLeft (lowerToUpper r j) (degreeOfFunctorIso r j F hinj).hom =
      ((ofFunctor r j F).degreeRestrictionIso hinj).hom := by
  ext x
  simp only [degreeOfFunctorIso, degreeRestrictionIso, Iso.trans_hom, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Iso.symm_hom, Functor.associator_inv_app,
    NatIso.ofComponents_hom_app, indexInclusionIso, ofFunctorIso, eqToIso, restrictionIso,
    Category.id_comp]
  have h := ofFunctor_toFunctor_map r j F (eqToHom (degreeIndex_obj_lower r j x))
  simp only [ofFunctorObjIso, InducedCategory.eqToHom_hom] at h
  change (ofFunctor r j F).toFunctor.map (eqToHom (degreeIndex_obj_lower r j x)) ≫
      𝟙 (F.obj x.obj) =
    (ofFunctorObjIso r j F ((degreeIndex r j hinj).obj ((lowerToUpper r j).obj x))).hom ≫
      F.map (eqToHom (degreeIndexObj_eq r j hinj ((lowerToUpper r j).obj x))) at h
  change (ofFunctorObjIso r j F ((degreeIndex r j hinj).obj ((lowerToUpper r j).obj x))).hom ≫
      F.map (eqToHom (degreeIndexObj_eq r j hinj ((lowerToUpper r j).obj x))) =
    (ofFunctor r j F).toFunctor.map (eqToHom (degreeIndex_obj_lower r j x)) ≫ 𝟙 (F.obj x.obj)
  exact h.symm

end SerrePositivity.Reedy.BoundaryExtension
