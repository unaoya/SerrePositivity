module
public import SerrePositivity.DifferentialGraded.Derived.BimoduleCompositionAssociatorNaturality

/-! # 全導来結合比較の両辺を束ねる関手族 -/
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

def derivedBimoduleAssociatorSource (hE : localHomKFlat A E) (hF : localHomKFlat A F) :
    DerivedBimoduleCategory A E F ⥤
      (DerivedBimoduleCategory A C E ⥤
        (DerivedBimoduleCategory A B C ⥤ DerivedBimoduleCategory A B F)) :=
  derivedBimoduleComposeFunctor A B E F hF ⋙
    whiskeringRight (DerivedBimoduleCategory A B C) (DerivedBimoduleCategory A B E)
      (DerivedBimoduleCategory A B F) ⋙
    (whiskeringLeft (DerivedBimoduleCategory A C E)
      (DerivedBimoduleCategory A B C ⥤ DerivedBimoduleCategory A B E)
      (DerivedBimoduleCategory A B C ⥤ DerivedBimoduleCategory A B F)).obj
        (derivedBimoduleComposeFunctor A B C E hE)

def derivedBimoduleAssociatorTarget (hF : localHomKFlat A F) :
    DerivedBimoduleCategory A E F ⥤
      (DerivedBimoduleCategory A C E ⥤
        (DerivedBimoduleCategory A B C ⥤ DerivedBimoduleCategory A B F)) :=
  derivedBimoduleComposeFunctor A C E F hF ⋙
    (whiskeringRight (DerivedBimoduleCategory A C E) (DerivedBimoduleCategory A C F)
      (DerivedBimoduleCategory A B C ⥤ DerivedBimoduleCategory A B F)).obj
        (derivedBimoduleComposeFunctor A B C F hF)

/-- 後の因子を固定し、中間因子の閉零対象上で束ねた結合比較。 -/
def derivedBimoduleAssociatorMiddleBaseIso (hE : localHomKFlat A E)
    (hF : localHomKFlat A F) (R : BimoduleCategory A E F) :
    bimoduleToDerived A C E ⋙
        (derivedBimoduleAssociatorSource A B C E F hE hF).obj
          ((bimoduleToDerived A E F).obj R) ≅
      bimoduleToDerived A C E ⋙
        (derivedBimoduleAssociatorTarget A B C E F hF).obj
          ((bimoduleToDerived A E F).obj R) :=
  NatIso.ofComponents (fun Q => derivedBimoduleAssociatorBaseIso A B C E F hE hF Q R)
    (fun {Q Q'} f => by
      change whiskerRight
          ((derivedBimoduleComposeFunctor A B C E hE).map ((bimoduleToDerived A C E).map f))
          ((derivedBimoduleComposeFunctor A B E F hF).obj ((bimoduleToDerived A E F).obj R)) ≫
        (derivedBimoduleAssociatorBaseIso A B C E F hE hF Q' R).hom =
        (derivedBimoduleAssociatorBaseIso A B C E F hE hF Q R).hom ≫
          (derivedBimoduleComposeFunctor A B C F hF).map
            (((derivedBimoduleComposeFunctor A C E F hF).obj
              ((bimoduleToDerived A E F).obj R)).map ((bimoduleToDerived A C E).map f))
      have h := derivedBimoduleAssociatorBaseIso_naturality A B C E F hE hF f (𝟙 R)
      simpa only [derivedBimoduleComposePairMap, derivedBimoduleComposeInnerMap,
        CategoryTheory.Functor.map_id, whiskerLeft_id', Category.comp_id, NatTrans.id_app]
        using h)

end SerrePositivity.DifferentialGraded.BimoduleTensor
