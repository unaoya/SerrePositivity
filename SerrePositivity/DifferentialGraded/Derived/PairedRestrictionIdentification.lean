module
public import SerrePositivity.DifferentialGraded.Bimodule.PairedRestrictionPresentation
public import SerrePositivity.DifferentialGraded.Derived.MiddleRestrictionIdentification
public import SerrePositivity.DifferentialGraded.Derived.BimoduleLiftIso

/-! # 両端制限と既存の積dg圏表示による導来制限の比較 -/
@[expose] public section
noncomputable section
universe u v w z t
namespace SerrePositivity.DifferentialGraded
open CategoryTheory BimoduleTensorModule
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (C : Type w) [DGCategory A C] [Small.{u} C]
  (D : Type z) [DGCategory A D] [Small.{u} D]
  (E : Type t) [DGCategory A E] [Small.{u} E]
  (F : DGFunctor A D B) (G : DGFunctor A E C)

/-- 直接両端制限は、既存の積dg圏表示によるbimodule制限に自然同型。 -/
def pairedRestrictionIso :
    BimoduleCategory.pairedRestrictionFunctor A B C D E F G ≅
      bimoduleRestriction A D E B C F G :=
  (Functor.rightUnitor _).symm ≪≫
    Functor.isoWhiskerLeft (BimoduleCategory.pairedRestrictionFunctor A B C D E F G)
      (rightModuleCounitIso A D E).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (pairedRestrictionPresentationIso A B C D E F G)
      (rightModuleBimoduleEquivalence A D E).functor ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerRight (rightModuleInverseIso A B C)
      (moduleRestriction A (DGTensorCategory A Dᵒᵖ E)ᵒᵖ (DGTensorCategory A Bᵒᵖ C)ᵒᵖ
        (bimoduleRestrictionIndex A D E B C F G) ⋙
          (rightModuleBimoduleEquivalence A D E).functor)

/-- 直接両端制限と既存の全導来制限の表示square。 -/
def pairedRestrictionDerivedIso :
    BimoduleCategory.pairedRestrictionFunctor A B C D E F G ⋙ bimoduleToDerived A D E ≅
      bimoduleToDerived A B C ⋙ derivedBimoduleRestriction A D E B C F G :=
  Functor.isoWhiskerRight (pairedRestrictionIso A B C D E F G) (bimoduleToDerived A D E) ≪≫
    (eqToIso (derivedBimoduleRestriction_fac A D E B C F G)).symm

/-- 左、次に右の二つの既存導来制限の、直接制限からの表示。 -/
def pairedRestrictionPartialPresentationIso :
    BimoduleCategory.pairedRestrictionFunctor A B C D E F G ⋙ bimoduleToDerived A D E ≅
      bimoduleToDerived A B C ⋙
        (derivedBimoduleRestriction A B E B C (DGFunctor.id B) G ⋙
          derivedBimoduleRestriction A D E B E F (DGFunctor.id E)) :=
  Functor.isoWhiskerLeft (BimoduleCategory.middleLeftRestrictionFunctor A B C E G)
      (middleRightRestrictionDerivedIso A B D F E) ≪≫
    Functor.isoWhiskerRight (middleLeftRestrictionDerivedIso A B C E G)
      (derivedBimoduleRestriction A D E B E F (DGFunctor.id E))

def pairedRestrictionPartialPreIso :
    bimoduleToDerived A B C ⋙
        (derivedBimoduleRestriction A B E B C (DGFunctor.id B) G ⋙
          derivedBimoduleRestriction A D E B E F (DGFunctor.id E)) ≅
      bimoduleToDerived A B C ⋙ derivedBimoduleRestriction A D E B C F G :=
  (pairedRestrictionPartialPresentationIso A B C D E F G).symm ≪≫
    pairedRestrictionDerivedIso A B C D E F G

/-- 左制限、右制限の順の合成は、既存の同時導来制限へ自然に比較できる。 -/
def pairedRestrictionPartialDerivedIso :
    derivedBimoduleRestriction A B E B C (DGFunctor.id B) G ⋙
        derivedBimoduleRestriction A D E B E F (DGFunctor.id E) ≅
      derivedBimoduleRestriction A D E B C F G :=
  bimoduleDerivedIsoOfPrecomp A B C _ _ (pairedRestrictionPartialPreIso A B C D E F G)

lemma pairedRestrictionPartialDerivedIso_hom_app (P : BimoduleCategory A B C) :
    (pairedRestrictionPartialDerivedIso A B C D E F G).hom.app
        ((bimoduleToDerived A B C).obj P) =
      (pairedRestrictionPartialPreIso A B C D E F G).hom.app P :=
  bimoduleDerivedIsoOfPrecomp_hom_app A B C _ _ _ P

/-- 右、次に左の二つの既存導来制限の、直接制限からの表示。 -/
def pairedRestrictionReversePresentationIso :
    (BimoduleCategory.middleRightRestrictionFunctor A B D C F ⋙
        BimoduleCategory.middleLeftRestrictionFunctor A D C E G) ⋙ bimoduleToDerived A D E ≅
      bimoduleToDerived A B C ⋙
        (derivedBimoduleRestriction A D C B C F (DGFunctor.id C) ⋙
          derivedBimoduleRestriction A D E D C (DGFunctor.id D) G) :=
  Functor.isoWhiskerLeft (BimoduleCategory.middleRightRestrictionFunctor A B D C F)
      (middleLeftRestrictionDerivedIso A D C E G) ≪≫
    Functor.isoWhiskerRight (middleRightRestrictionDerivedIso A B D F C)
      (derivedBimoduleRestriction A D E D C (DGFunctor.id D) G)

def pairedRestrictionReversePreIso :
    bimoduleToDerived A B C ⋙
        (derivedBimoduleRestriction A D C B C F (DGFunctor.id C) ⋙
          derivedBimoduleRestriction A D E D C (DGFunctor.id D) G) ≅
      bimoduleToDerived A B C ⋙ derivedBimoduleRestriction A D E B C F G :=
  (pairedRestrictionReversePresentationIso A B C D E F G).symm ≪≫
    Functor.isoWhiskerRight
      (BimoduleCategory.pairedRestrictionInterchangeIso A B C D E F G).symm
      (bimoduleToDerived A D E) ≪≫
    pairedRestrictionDerivedIso A B C D E F G

/-- 右制限、左制限の順も、同じ既存の同時導来制限へ自然に比較できる。 -/
def pairedRestrictionReverseDerivedIso :
    derivedBimoduleRestriction A D C B C F (DGFunctor.id C) ⋙
        derivedBimoduleRestriction A D E D C (DGFunctor.id D) G ≅
      derivedBimoduleRestriction A D E B C F G :=
  bimoduleDerivedIsoOfPrecomp A B C _ _ (pairedRestrictionReversePreIso A B C D E F G)

lemma pairedRestrictionReverseDerivedIso_hom_app (P : BimoduleCategory A B C) :
    (pairedRestrictionReverseDerivedIso A B C D E F G).hom.app
        ((bimoduleToDerived A B C).obj P) =
      (pairedRestrictionReversePreIso A B C D E F G).hom.app P :=
  bimoduleDerivedIsoOfPrecomp_hom_app A B C _ _ _ P

end SerrePositivity.DifferentialGraded
