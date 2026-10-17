module
public import SerrePositivity.DifferentialGraded.Derived.BimoduleEndpointRestriction
public import SerrePositivity.DifferentialGraded.Derived.BimoduleMiddleFullComposition

/-! # 三つのdg圏を同時に制限した全導来bimodule合成比較 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z t s r
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory CategoryTheory.Functor
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (D : Type w) [DGCategory A D] [Small.{u} D]
  (C : Type z) [DGCategory A C] [Small.{u} C]
  (K : Type t) [DGCategory A K] [Small.{u} K]
  (E : Type s) [DGCategory A E] [Small.{u} E]
  (L : Type r) [DGCategory A L] [Small.{u} L]
  (F : DGFunctor A D B) (G : DGFunctor A K C) (H : DGFunctor A L E)
  (hE : localHomKFlat A E) (hL : localHomKFlat A L)

/-- 三つのdg圏に沿う既存の同時導来制限を両因子へ適用してから合成するsource。 -/
def simultaneousRestrictionDerivedSource : DerivedBimoduleCategory A C E ⥤
    (DerivedBimoduleCategory A B C ⥤ DerivedBimoduleCategory A D L) :=
  derivedBimoduleRestriction A K L C E G H ⋙ derivedBimoduleComposeFunctor A D K L hL ⋙
    (whiskeringLeft _ _ _).obj (derivedBimoduleRestriction A D K B C F G)

/-- 既存の外側左右制限を施したうえで、中間圏比較へ適用するsource表示。 -/
def simultaneousRestrictionMiddleSource : DerivedBimoduleCategory A C E ⥤
    (DerivedBimoduleCategory A B C ⥤ DerivedBimoduleCategory A D L) :=
  derivedBimoduleRestriction A C L C E (DGFunctor.id C) H ⋙
    middleRestrictionDerivedSource A D C K L G hL ⋙
      (whiskeringLeft _ _ _).obj (derivedBimoduleRestriction A D C B C F (DGFunctor.id C))

/-- 両因子の既存の同時制限を、外側制限と中間制限へ分ける独立のsource同型。 -/
def simultaneousRestrictionSourceIso :
    simultaneousRestrictionDerivedSource A B D C K E L F G H hL ≅
      simultaneousRestrictionMiddleSource A B D C K E L F G H hL :=
  Functor.isoWhiskerRight (pairedRestrictionPartialDerivedIso A C E K L G H).symm
      (derivedBimoduleComposeFunctor A D K L hL ⋙
        (whiskeringLeft _ _ _).obj (derivedBimoduleRestriction A D K B C F G)) ≪≫
    Functor.isoWhiskerLeft
      (derivedBimoduleRestriction A C L C E (DGFunctor.id C) H ⋙
        derivedBimoduleRestriction A K L C L G (DGFunctor.id L) ⋙
          derivedBimoduleComposeFunctor A D K L hL)
      ((whiskeringLeft _ _ _).mapIso (pairedRestrictionReverseDerivedIso A B C D K F G).symm)

/-- 任意の三つのdg関手に沿う、既存の全導来合成間の比較自然変換。 -/
def simultaneousRestrictionDerivedComparison :
    simultaneousRestrictionDerivedSource A B D C K E L F G H hL ⟶
      endpointRestrictionDerivedTarget A B D C E L F H hE :=
  (simultaneousRestrictionSourceIso A B D C K E L F G H hL).hom ≫
    whiskerRight
      (whiskerLeft (derivedBimoduleRestriction A C L C E (DGFunctor.id C) H)
        (derivedMiddleRestrictionNatTrans A D C K L G hL))
      ((whiskeringLeft _ _ _).obj (derivedBimoduleRestriction A D C B C F (DGFunctor.id C))) ≫
    (derivedBimoduleComposeEndpointRestrictionIso A B D C E L F H hE hL).hom

/-- 中間関手だけが準同値なら、三圏を同時制限した比較は両変数で自然な同型。 -/
def derivedBimoduleComposeRestrictionIso (hG : QuasiEquivalence G) :
    simultaneousRestrictionDerivedSource A B D C K E L F G H hL ≅
      endpointRestrictionDerivedTarget A B D C E L F H hE :=
  simultaneousRestrictionSourceIso A B D C K E L F G H hL ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft (derivedBimoduleRestriction A C L C E (DGFunctor.id C) H)
        (derivedMiddleRestrictionIso A D C K L G hG hL))
      ((whiskeringLeft _ _ _).obj (derivedBimoduleRestriction A D C B C F (DGFunctor.id C))) ≪≫
    derivedBimoduleComposeEndpointRestrictionIso A B D C E L F H hE hL

lemma derivedBimoduleComposeRestrictionIso_hom (hG : QuasiEquivalence G) :
    (derivedBimoduleComposeRestrictionIso A B D C K E L F G H hE hL hG).hom =
      simultaneousRestrictionDerivedComparison A B D C K E L F G H hE hL := rfl

end SerrePositivity.DifferentialGraded.BimoduleTensor
