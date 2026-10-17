module
public import SerrePositivity.DifferentialGraded.Bimodule.PairedRestrictionCoherence
public import SerrePositivity.DifferentialGraded.Derived.PairedRestrictionIdentification

/-! # 既存の両端導来制限の恒等・合成比較とモデル計算 -/
@[expose] public section
noncomputable section
universe u v w z t s r
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (C : Type w) [DGCategory A C] [Small.{u} C]

def pairedRestrictionIdDerivedPreIso :
    bimoduleToDerived A B C ⋙
        derivedBimoduleRestriction A B C B C (DGFunctor.id B) (DGFunctor.id C) ≅
      bimoduleToDerived A B C ⋙ 𝟭 (DerivedBimoduleCategory A B C) :=
  (pairedRestrictionDerivedIso A B C B C (DGFunctor.id B) (DGFunctor.id C)).symm ≪≫
    Functor.isoWhiskerRight (BimoduleCategory.pairedRestrictionIdIso A B C)
      (bimoduleToDerived A B C)

/-- 既存の同時導来制限の恒等比較。 -/
def pairedRestrictionIdDerivedIso :
    derivedBimoduleRestriction A B C B C (DGFunctor.id B) (DGFunctor.id C) ≅
      𝟭 (DerivedBimoduleCategory A B C) :=
  bimoduleDerivedIsoOfPrecomp A B C _ _ (pairedRestrictionIdDerivedPreIso A B C)

lemma pairedRestrictionIdDerivedIso_hom_app (P : BimoduleCategory A B C) :
    (pairedRestrictionIdDerivedIso A B C).hom.app ((bimoduleToDerived A B C).obj P) =
      (pairedRestrictionIdDerivedPreIso A B C).hom.app P :=
  bimoduleDerivedIsoOfPrecomp_hom_app A B C _ _ _ P

variable (E : Type z) [DGCategory A E] [Small.{u} E]
  (L : Type t) [DGCategory A L] [Small.{u} L]
  (D : Type s) [DGCategory A D] [Small.{u} D]
  (K : Type r) [DGCategory A K] [Small.{u} K]
  (F : DGFunctor A D E) (G : DGFunctor A E B)
  (H : DGFunctor A K L) (I : DGFunctor A L C)

def pairedRestrictionCompDerivedPreIso :
    bimoduleToDerived A B C ⋙
        (derivedBimoduleRestriction A E L B C G I ⋙
          derivedBimoduleRestriction A D K E L F H) ≅
      bimoduleToDerived A B C ⋙
        derivedBimoduleRestriction A D K B C (F.comp G) (H.comp I) :=
  Functor.isoWhiskerRight (pairedRestrictionDerivedIso A B C E L G I).symm
      (derivedBimoduleRestriction A D K E L F H) ≪≫
    Functor.isoWhiskerLeft (BimoduleCategory.pairedRestrictionFunctor A B C E L G I)
      (pairedRestrictionDerivedIso A E L D K F H).symm ≪≫
    Functor.isoWhiskerRight
      (BimoduleCategory.pairedRestrictionCompIso A B C E L D K F G H I)
      (bimoduleToDerived A D K) ≪≫
    pairedRestrictionDerivedIso A B C D K (F.comp G) (H.comp I)

/-- 二つの既存同時導来制限の合成を、合成dg関手による既存制限へ送る。 -/
def pairedRestrictionCompDerivedIso :
    derivedBimoduleRestriction A E L B C G I ⋙ derivedBimoduleRestriction A D K E L F H ≅
      derivedBimoduleRestriction A D K B C (F.comp G) (H.comp I) :=
  bimoduleDerivedIsoOfPrecomp A B C _ _
    (pairedRestrictionCompDerivedPreIso A B C E L D K F G H I)

lemma pairedRestrictionCompDerivedIso_hom_app (P : BimoduleCategory A B C) :
    (pairedRestrictionCompDerivedIso A B C E L D K F G H I).hom.app
        ((bimoduleToDerived A B C).obj P) =
      (pairedRestrictionCompDerivedPreIso A B C E L D K F G H I).hom.app P :=
  bimoduleDerivedIsoOfPrecomp_hom_app A B C _ _ _ P

end SerrePositivity.DifferentialGraded
