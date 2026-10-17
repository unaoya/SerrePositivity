module
public import SerrePositivity.DifferentialGraded.Derived.FunctorExtensionAdjunction
public import SerrePositivity.DifferentialGraded.Module.FunctorExtensionRepresentableUnit
public import SerrePositivity.DifferentialGraded.Derived.FunctorExtensionRepresentable

/-! # 導来単位と射影解像度上の実際の単位の計算 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D E)

private lemma rightAdjointIso_unit {C : Type*} {T : Type*}
    [Category* C] [Category* T] {L : C ⥤ T} {R R' : T ⥤ C}
    (adj : L ⊣ R) (e : R ≅ R') (X : C) :
    (adj.ofNatIsoRight e).unit.app X = adj.unit.app X ≫ e.hom.app (L.obj X) := by
  rw [← Adjunction.homEquiv_id, Adjunction.homEquiv_ofNatIsoRight_apply,
    Adjunction.homEquiv_id]

private lemma functorEqIso_inv_app {C : Type*} {T : Type*}
    [Category* C] [Category* T] {G H : C ⥤ T} (h : G = H) (X : C) :
    (eqToIso h).inv.app X = (eqToIso (congrArg (fun J => J.obj X) h)).inv := by
  cases h
  rfl

lemma dgModuleExtensionRestrictionAdjunction_unit (M : ModuleCategory A D) :
    (dgModuleExtensionRestrictionAdjunction A D E F).unit.app M =
      functorExtensionUnit A D E F (ForgetEnrichment.to (Complex A) M) := rfl

lemma dgModuleEnrichedRestrictionAdjunction_unit (M : ModuleCategory A D) :
    (dgModuleEnrichedRestrictionAdjunction A D E F).unit.app M =
      functorExtensionUnit A D E F (ForgetEnrichment.to (Complex A) M) := by
  have h := rightAdjointIso_unit (dgModuleExtensionRestrictionAdjunction A D E F)
    (eqToIso (dgModuleRestriction_onClosed_eq A D E F.op)).symm M
  have hi : (eqToIso (dgModuleRestriction_onClosed_eq A D E F.op)).symm.hom.app
      ((dgModuleExtension A D E F).onClosed.obj M) = 𝟙 _ := by
    change (eqToIso (dgModuleRestriction_onClosed_eq A D E F.op)).inv.app
      ((dgModuleExtension A D E F).onClosed.obj M) = _
    rw [functorEqIso_inv_app]
    rfl
  refine h.trans ?_
  refine (congrArg (fun t => (dgModuleExtensionRestrictionAdjunction A D E F).unit.app M ≫ t)
    hi).trans ?_
  exact (Category.comp_id _).trans (dgModuleExtensionRestrictionAdjunction_unit A D E F M)

lemma dgDerivedExtensionRestrictionAdjunction_homEquiv :
    (dgDerivedExtensionRestrictionAdjunction A D E F).homEquiv =
      dgDerivedExtensionHomEquiv A D E F :=
  Adjunction.mkOfHomEquiv_homEquiv _

lemma dgDerivedExtensionUnit_computation (M : ModuleCategory A D) :
    (dgDerivedExtensionUnit A D E F).app ((moduleToDerived A D).obj M) ≫
      (dgDerivedRestriction A D E F).map
        (dgDerivedExtensionResolutionComputation A D E F
          (moduleCanonicalProjectiveResolution A D M)).hom =
    (moduleDerivedIso A D (moduleCanonicalProjectiveResolution A D M).π
      (moduleCanonicalProjectiveResolution A D M).quasiIso).inv ≫
      (moduleToDerived A D).map (functorExtensionUnit A D E F
        (ForgetEnrichment.to (Complex A) (moduleCanonicalProjectiveResolution A D M).obj)) ≫
      (dgDerivedRestrictionComputation A D E F
        ((dgModuleExtension A D E F).onClosed.obj
          (moduleCanonicalProjectiveResolution A D M).obj)).inv := by
  have h := (dgDerivedExtensionRestrictionAdjunction A D E F).homEquiv_unit
    ((moduleToDerived A D).obj M)
    ((moduleToDerived A E).obj ((dgModuleExtension A D E F).onClosed.obj
      (moduleCanonicalProjectiveResolution A D M).obj))
    (dgDerivedExtensionResolutionComputation A D E F
      (moduleCanonicalProjectiveResolution A D M)).hom
  refine h.symm.trans ?_
  rw [dgDerivedExtensionRestrictionAdjunction_homEquiv]
  change dgDerivedExtensionHomEquivOnModules A D E F M
    ((dgModuleExtension A D E F).onClosed.obj
      (moduleCanonicalProjectiveResolution A D M).obj)
    (dgDerivedExtensionResolutionComputation A D E F
      (moduleCanonicalProjectiveResolution A D M)).hom = _
  rw [dgDerivedExtensionHomEquivOnModules_apply, Iso.inv_hom_id]
  rw [← CategoryTheory.Functor.map_id (moduleToDerived A E)]
  rw [dgProjectiveDerivedExtensionHomEquiv_map, Adjunction.homEquiv_id,
    dgModuleEnrichedRestrictionAdjunction_unit]

end SerrePositivity.DifferentialGraded
