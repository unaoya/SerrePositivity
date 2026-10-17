module
public import SerrePositivity.DifferentialGraded.Derived.MiddleRestrictionComposition

/-! # 二段階の直接制限から既存の導来制限への表示同型 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z t
namespace SerrePositivity.DifferentialGraded
open CategoryTheory CategoryTheory.Functor
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (D : Type w) [DGCategory A D] [Small.{u} D]
  (E : Type z) [DGCategory A E] [Small.{u} E]
  (T : Type t) [DGCategory A T] [Small.{u} T]
  (F : DGFunctor A D E) (G : DGFunctor A E T)

/-- 二段階の直接左制限の局所化を、既存の二段階導来制限へ送る。 -/
def middleLeftIteratedDerivedIso :
    BimoduleCategory.middleLeftRestrictionFunctor A B T E G ⋙
        BimoduleCategory.middleLeftRestrictionFunctor A B E D F ⋙ bimoduleToDerived A B D ≅
      bimoduleToDerived A B T ⋙
        derivedBimoduleRestriction A B E B T (DGFunctor.id B) G ⋙
          derivedBimoduleRestriction A B D B E (DGFunctor.id B) F :=
  Functor.isoWhiskerLeft (BimoduleCategory.middleLeftRestrictionFunctor A B T E G)
      (middleLeftRestrictionDerivedIso A B E D F) ≪≫
    Functor.isoWhiskerRight (middleLeftRestrictionDerivedIso A B T E G)
      (derivedBimoduleRestriction A B D B E (DGFunctor.id B) F)

lemma middleLeftIteratedDerivedIso_normalize :
    (middleLeftIteratedDerivedIso A B D E T F G).hom ≫
        whiskerLeft (bimoduleToDerived A B T) (middleLeftDerivedCompIso A B D E T F G).hom =
      whiskerRight (BimoduleCategory.middleLeftRestrictionCompIso A B D E T F G).hom
          (bimoduleToDerived A B D) ≫
        (middleLeftRestrictionDerivedIso A B T D (F.comp G)).hom := by
  apply NatTrans.ext
  funext P
  simpa only [middleLeftIteratedDerivedIso, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom, whiskerLeft_app,
    whiskerRight_app, BimoduleCategory.middleLeftRestrictionCompIso, NatIso.ofComponents_hom_app,
    Category.assoc] using
    middleLeftDerivedCompIso_presentation A B D E T F G P

/-- 二段階の直接右制限の局所化を、既存の二段階導来制限へ送る。 -/
def middleRightIteratedDerivedIso :
    BimoduleCategory.middleRightRestrictionFunctor A T E B G ⋙
        BimoduleCategory.middleRightRestrictionFunctor A E D B F ⋙ bimoduleToDerived A D B ≅
      bimoduleToDerived A T B ⋙
        derivedBimoduleRestriction A E B T B G (DGFunctor.id B) ⋙
          derivedBimoduleRestriction A D B E B F (DGFunctor.id B) :=
  Functor.isoWhiskerLeft (BimoduleCategory.middleRightRestrictionFunctor A T E B G)
      (middleRightRestrictionDerivedIso A E D F B) ≪≫
    Functor.isoWhiskerRight (middleRightRestrictionDerivedIso A T E G B)
      (derivedBimoduleRestriction A D B E B F (DGFunctor.id B))

lemma middleRightIteratedDerivedIso_normalize :
    (middleRightIteratedDerivedIso A B D E T F G).hom ≫
        whiskerLeft (bimoduleToDerived A T B) (middleRightDerivedCompIso A B D E T F G).hom =
      whiskerRight (BimoduleCategory.middleRightRestrictionCompIso A D B E T F G).hom
          (bimoduleToDerived A D B) ≫
        (middleRightRestrictionDerivedIso A T D (F.comp G) B).hom := by
  apply NatTrans.ext
  funext Q
  simpa only [middleRightIteratedDerivedIso, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom, whiskerLeft_app,
    whiskerRight_app, BimoduleCategory.middleRightRestrictionCompIso, NatIso.ofComponents_hom_app,
    Category.assoc] using
    middleRightDerivedCompIso_presentation A B D E T F G Q

end SerrePositivity.DifferentialGraded
