module
public import SerrePositivity.DifferentialGraded.Derived.AssociatorLeftRestrictionFamilies

/-! # 全三因子に対する導来結合子と外側左制限のcoherence -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z t s
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory CategoryTheory.Functor
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (C : Type w) [DGCategory A C] [Small.{u} C]
  (E : Type z) [DGCategory A E] [Small.{u} E]
  (T : Type t) [DGCategory A T] [Small.{u} T]
  (D : Type s) [DGCategory A D] [Small.{u} D] (G : DGFunctor A D T)
  (hE : localHomKFlat A E) (hT : localHomKFlat A T) (hD : localHomKFlat A D)

local notation "L" => derivedBimoduleRestriction A B D B T (DGFunctor.id B) G
local notation "LE" => derivedBimoduleRestriction A E D E T (DGFunctor.id E) G

/-- モデル上の一致を後二つの全導来変数へ持ち上げた、関手族間の経路の一致。 -/
lemma leftRestrictionAssociatorPaths_eq :
    leftRestrictionAssociatorLeftPath A B C E T D G hE hT hD =
      leftRestrictionAssociatorRightPath A B C E T D G hE hT hD := by
  apply rightKFlatDerivedNatTrans_ext A E T hT
  intro R
  apply rightKFlatDerivedNatTrans_ext A C E hE
  intro Q
  rw [leftRestrictionAssociatorLeftPath_app, leftRestrictionAssociatorRightPath_app]
  exact derivedBimoduleAssociator_leftRestriction_rightKFlat A B C E T D G hE hT hD Q R

/-- 任意の全導来後二因子と任意の導来前因子について、外側左制限が結合子を保つ。 -/
lemma derivedBimoduleAssociator_leftRestriction
    (Q : DerivedBimoduleCategory A C E) (R : DerivedBimoduleCategory A E T) :
    (derivedBimoduleAssociator A B C E D hE hD Q ((LE).obj R)).hom ≫
      (derivedBimoduleComposeFunctor A B C D hD).map
        (((derivedBimoduleComposeLeftRestrictionIso A C E T D G hT hD).inv.app R).app Q) ≫
      (derivedBimoduleComposeLeftRestrictionIso A B C T D G hT hD).inv.app
        (((derivedBimoduleComposeFunctor A C E T hT).obj R).obj Q) =
    whiskerLeft ((derivedBimoduleComposeFunctor A B C E hE).obj Q)
        ((derivedBimoduleComposeLeftRestrictionIso A B E T D G hT hD).inv.app R) ≫
      whiskerRight (derivedBimoduleAssociator A B C E T hE hT Q R).hom L := by
  have h := NatTrans.congr_app
    (NatTrans.congr_app (leftRestrictionAssociatorPaths_eq A B C E T D G hE hT hD) R) Q
  simpa only [leftRestrictionAssociatorLeftPath_app,
    leftRestrictionAssociatorRightPath_app] using h

end SerrePositivity.DifferentialGraded.BimoduleTensor
