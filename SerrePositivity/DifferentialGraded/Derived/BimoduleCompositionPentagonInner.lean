module
public import SerrePositivity.DifferentialGraded.Derived.BimoduleCompositionPentagonPaths
public import SerrePositivity.DifferentialGraded.Derived.BimoduleTensorPentagon

/-! # 五角図式の内側の結合射とK-flat三因子の値比較 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z t
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory CategoryTheory.Functor
variable (A : Type u) [CommRing A] (C : Type v) (E : Type w) (F : Type z) (G : Type t)
  [DGCategory A C] [DGCategory A E] [DGCategory A F] [DGCategory A G]
  [Small.{u} C] [Small.{u} E] [Small.{u} F] [Small.{u} G]

def derivedBimoduleTripleLeftValueIso (hF : localHomKFlat A F) (hG : localHomKFlat A G)
    (Q : RightKFlatBimoduleCategory A C E) (R : RightKFlatBimoduleCategory A E F)
    (S : RightKFlatBimoduleCategory A F G) :
    ((derivedBimoduleComposeFunctor A C F G hG).obj ((bimoduleToDerived A F G).obj S.obj)).obj
        (((derivedBimoduleComposeFunctor A C E F hF).obj
          ((bimoduleToDerived A E F).obj R.obj)).obj ((bimoduleToDerived A C E).obj Q.obj)) ≅
      (bimoduleToDerived A C G).obj
        (rightKFlatCompose A C F G (rightKFlatCompose A C E F Q R) S).obj :=
  derivedBimoduleComposeInnerComparisonIso A C F G hG (rightKFlatCompose A C E F Q R) S
    (derivedBimoduleComposeKFlatValueIso A C E F hF R Q.obj) (Iso.refl _)

def derivedBimoduleTripleRightValueIso (hG : localHomKFlat A G)
    (Q : RightKFlatBimoduleCategory A C E) (R : RightKFlatBimoduleCategory A E F)
    (S : RightKFlatBimoduleCategory A F G) :
    ((derivedBimoduleComposeFunctor A C E G hG).obj
        (((derivedBimoduleComposeFunctor A E F G hG).obj
          ((bimoduleToDerived A F G).obj S.obj)).obj ((bimoduleToDerived A E F).obj R.obj))).obj
            ((bimoduleToDerived A C E).obj Q.obj) ≅
      (bimoduleToDerived A C G).obj
        (rightKFlatCompose A C E G Q (rightKFlatCompose A E F G R S)).obj :=
  derivedBimoduleComposeInnerComparisonIso A C E G hG Q (rightKFlatCompose A E F G R S)
    (Iso.refl _) (derivedBimoduleComposeKFlatValueIso A E F G hG S R.obj)

lemma derivedBimoduleTripleValueIso_associator (hF : localHomKFlat A F)
    (hG : localHomKFlat A G) (Q : RightKFlatBimoduleCategory A C E)
    (R : RightKFlatBimoduleCategory A E F) (S : RightKFlatBimoduleCategory A F G) :
    (derivedBimoduleAssociator A C E F G hF hG
        ((bimoduleToDerived A E F).obj R.obj) ((bimoduleToDerived A F G).obj S.obj)).hom.app
          ((bimoduleToDerived A C E).obj Q.obj) ≫
        (derivedBimoduleTripleRightValueIso A C E F G hG Q R S).hom =
      (derivedBimoduleTripleLeftValueIso A C E F G hF hG Q R S).hom ≫
        (bimoduleToDerived A C G).map
          (associatorIso A C E F G (BimoduleCategory.underlying A C E Q.obj)
            (BimoduleCategory.underlying A E F R.obj)
            (BimoduleCategory.underlying A F G S.obj)).hom := by
  have h := NatTrans.congr_app (derivedBimoduleAssociatorIso_kFlat_fac A C E F G hF hG R S)
    ((bimoduleToDerived A C E).obj Q.obj)
  simp only [NatTrans.comp_app, whiskerRight_app, whiskerLeft_app,
    rightKFlatDerivedAssociator_base_app] at h
  simp only [derivedBimoduleAssociator, derivedBimoduleComposeKFlatValueIso,
    derivedBimoduleTripleLeftValueIso, derivedBimoduleTripleRightValueIso,
    derivedBimoduleComposeInnerComparisonIso, Iso.trans_hom, Iso.refl_hom,
    CategoryTheory.Functor.mapIso_hom, CategoryTheory.Functor.map_id,
    Iso.app_hom, NatTrans.id_app, Category.id_comp,
    Category.assoc] at h ⊢
  exact h

end SerrePositivity.DifferentialGraded.BimoduleTensor
