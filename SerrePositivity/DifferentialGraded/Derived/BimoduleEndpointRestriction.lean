module
public import SerrePositivity.DifferentialGraded.Derived.PairedRestrictionIdentification
public import SerrePositivity.DifferentialGraded.Derived.BimoduleLeftRestrictionFull
public import SerrePositivity.DifferentialGraded.Derived.BimoduleRightRestrictionFull

/-! # 合成の両端のdg圏の制限と全導来bimodule合成の比較 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z t s
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory CategoryTheory.Functor
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (D : Type w) [DGCategory A D] [Small.{u} D]
  (C : Type z) [DGCategory A C] [Small.{u} C]
  (E : Type t) [DGCategory A E] [Small.{u} E]
  (K : Type s) [DGCategory A K] [Small.{u} K]
  (F : DGFunctor A D B) (H : DGFunctor A K E)
  (hE : localHomKFlat A E) (hK : localHomKFlat A K)

/-- 両因子の外側の作用をそれぞれ制限してから合成する既存導来関手族。 -/
def endpointRestrictionDerivedSource : DerivedBimoduleCategory A C E ⥤
    (DerivedBimoduleCategory A B C ⥤ DerivedBimoduleCategory A D K) :=
  derivedBimoduleRestriction A C K C E (DGFunctor.id C) H ⋙
    derivedBimoduleComposeFunctor A D C K hK ⋙
      (whiskeringLeft _ _ _).obj (derivedBimoduleRestriction A D C B C F (DGFunctor.id C))

/-- 合成後の両端を、既存の同時導来制限で制限する関手族。 -/
def endpointRestrictionDerivedTarget : DerivedBimoduleCategory A C E ⥤
    (DerivedBimoduleCategory A B C ⥤ DerivedBimoduleCategory A D K) :=
  derivedBimoduleComposeFunctor A B C E hE ⋙
    (whiskeringRight _ _ _).obj (derivedBimoduleRestriction A D K B E F H)

/-- 外側左右の既存比較と両端制限の表示同型から作る、全導来合成比較。 -/
def derivedBimoduleComposeEndpointRestrictionIso :
    endpointRestrictionDerivedSource A B D C E K F H hK ≅
      endpointRestrictionDerivedTarget A B D C E K F H hE :=
  Functor.isoWhiskerLeft (derivedBimoduleRestriction A C K C E (DGFunctor.id C) H)
      (derivedBimoduleComposeRightRestrictionIso A B D C K F hK) ≪≫
    Functor.isoWhiskerRight
      (derivedBimoduleComposeLeftRestrictionIso A B C E K H hE hK).symm
      ((whiskeringRight _ _ _).obj
        (derivedBimoduleRestriction A D K B K F (DGFunctor.id K))) ≪≫
    Functor.isoWhiskerLeft (derivedBimoduleComposeFunctor A B C E hE)
      ((whiskeringRight _ _ _).mapIso (pairedRestrictionPartialDerivedIso A B E D K F H))

end SerrePositivity.DifferentialGraded.BimoduleTensor
