module
public import SerrePositivity.DifferentialGraded.Derived.BimoduleCompositionAssociatorFunctors

/-! # 全三因子に自然な導来bimodule合成の結合自然同型 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z t
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory CategoryTheory.Functor
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z) (F : Type t)
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [DGCategory A F]
  [Small.{u} B] [Small.{u} C] [Small.{u} E] [Small.{u} F]

def derivedBimoduleAssociatorMiddleIso (hE : localHomKFlat A E)
    (hF : localHomKFlat A F) (R : BimoduleCategory A E F) :
    (derivedBimoduleAssociatorSource A B C E F hE hF).obj ((bimoduleToDerived A E F).obj R) ≅
      (derivedBimoduleAssociatorTarget A B C E F hF).obj ((bimoduleToDerived A E F).obj R) :=
  Localization.liftNatIso (bimoduleToDerived A C E) (BimoduleCategory.quasiIso A C E)
    _ _ _ _ (derivedBimoduleAssociatorMiddleBaseIso A B C E F hE hF R)

lemma derivedBimoduleAssociatorMiddleIso_base_app (hE : localHomKFlat A E)
    (hF : localHomKFlat A F) (Q : BimoduleCategory A C E) (R : BimoduleCategory A E F) :
    (derivedBimoduleAssociatorMiddleIso A B C E F hE hF R).hom.app
        ((bimoduleToDerived A C E).obj Q) =
      (derivedBimoduleAssociatorBaseIso A B C E F hE hF Q R).hom := by
  have h := Localization.liftNatTrans_app (bimoduleToDerived A C E)
    (BimoduleCategory.quasiIso A C E)
    (bimoduleToDerived A C E ⋙ (derivedBimoduleAssociatorSource A B C E F hE hF).obj
      ((bimoduleToDerived A E F).obj R))
    (bimoduleToDerived A C E ⋙ (derivedBimoduleAssociatorTarget A B C E F hF).obj
      ((bimoduleToDerived A E F).obj R))
    ((derivedBimoduleAssociatorSource A B C E F hE hF).obj ((bimoduleToDerived A E F).obj R))
    ((derivedBimoduleAssociatorTarget A B C E F hF).obj ((bimoduleToDerived A E F).obj R))
    (derivedBimoduleAssociatorMiddleBaseIso A B C E F hE hF R).hom Q
  change (derivedBimoduleAssociatorMiddleIso A B C E F hE hF R).hom.app
    ((bimoduleToDerived A C E).obj Q) =
      𝟙 _ ≫ (derivedBimoduleAssociatorBaseIso A B C E F hE hF Q R).hom ≫ 𝟙 _ at h
  simpa only [Category.id_comp, Category.comp_id] using h

lemma derivedBimoduleAssociatorMiddleIso_naturality (hE : localHomKFlat A E)
    (hF : localHomKFlat A F) {R R' : BimoduleCategory A E F} (g : R ⟶ R') :
    (derivedBimoduleAssociatorSource A B C E F hE hF).map ((bimoduleToDerived A E F).map g) ≫
        (derivedBimoduleAssociatorMiddleIso A B C E F hE hF R').hom =
      (derivedBimoduleAssociatorMiddleIso A B C E F hE hF R).hom ≫
        (derivedBimoduleAssociatorTarget A B C E F hF).map ((bimoduleToDerived A E F).map g) := by
  apply bimoduleDerivedNatTrans_ext A C E
  intro Q
  simp only [NatTrans.comp_app, derivedBimoduleAssociatorMiddleIso_base_app]
  change whiskerLeft
      ((derivedBimoduleComposeFunctor A B C E hE).obj ((bimoduleToDerived A C E).obj Q))
      ((derivedBimoduleComposeFunctor A B E F hF).map ((bimoduleToDerived A E F).map g)) ≫
    (derivedBimoduleAssociatorBaseIso A B C E F hE hF Q R').hom =
    (derivedBimoduleAssociatorBaseIso A B C E F hE hF Q R).hom ≫
      (derivedBimoduleComposeFunctor A B C F hF).map
        (((derivedBimoduleComposeFunctor A C E F hF).map
          ((bimoduleToDerived A E F).map g)).app ((bimoduleToDerived A C E).obj Q))
  have h := derivedBimoduleAssociatorBaseIso_naturality A B C E F hE hF (𝟙 Q) g
  simpa only [derivedBimoduleComposePairMap, derivedBimoduleComposeInnerMap,
    CategoryTheory.Functor.map_id, whiskerRight_id', Category.id_comp] using h

def derivedBimoduleAssociatorOuterBaseIso (hE : localHomKFlat A E)
    (hF : localHomKFlat A F) :
    bimoduleToDerived A E F ⋙ derivedBimoduleAssociatorSource A B C E F hE hF ≅
      bimoduleToDerived A E F ⋙ derivedBimoduleAssociatorTarget A B C E F hF :=
  NatIso.ofComponents (derivedBimoduleAssociatorMiddleIso A B C E F hE hF)
    (fun g => derivedBimoduleAssociatorMiddleIso_naturality A B C E F hE hF g)

/-- 全後因子を指定準同型で局所化した関手族間の結合自然同型。 -/
def derivedBimoduleAssociatorIso (hE : localHomKFlat A E) (hF : localHomKFlat A F) :
    derivedBimoduleAssociatorSource A B C E F hE hF ≅
      derivedBimoduleAssociatorTarget A B C E F hF :=
  Localization.liftNatIso (bimoduleToDerived A E F) (BimoduleCategory.quasiIso A E F)
    _ _ _ _ (derivedBimoduleAssociatorOuterBaseIso A B C E F hE hF)

lemma derivedBimoduleAssociatorIso_outer_base_app (hE : localHomKFlat A E)
    (hF : localHomKFlat A F) (R : BimoduleCategory A E F) :
    (derivedBimoduleAssociatorIso A B C E F hE hF).hom.app ((bimoduleToDerived A E F).obj R) =
      (derivedBimoduleAssociatorMiddleIso A B C E F hE hF R).hom := by
  have h := Localization.liftNatTrans_app (bimoduleToDerived A E F)
    (BimoduleCategory.quasiIso A E F)
    (bimoduleToDerived A E F ⋙ derivedBimoduleAssociatorSource A B C E F hE hF)
    (bimoduleToDerived A E F ⋙ derivedBimoduleAssociatorTarget A B C E F hF)
    (derivedBimoduleAssociatorSource A B C E F hE hF)
    (derivedBimoduleAssociatorTarget A B C E F hF)
    (derivedBimoduleAssociatorOuterBaseIso A B C E F hE hF).hom R
  change (derivedBimoduleAssociatorIso A B C E F hE hF).hom.app
    ((bimoduleToDerived A E F).obj R) =
      𝟙 _ ≫ (derivedBimoduleAssociatorMiddleIso A B C E F hE hF R).hom ≫ 𝟙 _ at h
  simpa only [Category.id_comp, Category.comp_id] using h

lemma derivedBimoduleAssociatorIso_base_app (hE : localHomKFlat A E)
    (hF : localHomKFlat A F) (Q : BimoduleCategory A C E) (R : BimoduleCategory A E F) :
    (((derivedBimoduleAssociatorIso A B C E F hE hF).app
      ((bimoduleToDerived A E F).obj R)).app ((bimoduleToDerived A C E).obj Q)).hom =
      (derivedBimoduleAssociatorBaseIso A B C E F hE hF Q R).hom := by
  change ((derivedBimoduleAssociatorIso A B C E F hE hF).hom.app
    ((bimoduleToDerived A E F).obj R)).app ((bimoduleToDerived A C E).obj Q) = _
  rw [derivedBimoduleAssociatorIso_outer_base_app, derivedBimoduleAssociatorMiddleIso_base_app]

end SerrePositivity.DifferentialGraded.BimoduleTensor
