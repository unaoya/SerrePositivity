module
public import SerrePositivity.DifferentialGraded.Derived.AssociatorSecondMiddleRestrictionFamilies

/-! # 全導来三因子に対する第二中間制限と結合子のcoherence -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z t s
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory CategoryTheory.Functor
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (C : Type w) [DGCategory A C] [Small.{u} C]
  (D : Type z) [DGCategory A D] [Small.{u} D]
  (E : Type t) [DGCategory A E] [Small.{u} E]
  (T : Type s) [DGCategory A T] [Small.{u} T] (F : DGFunctor A D E)
  (hE : localHomKFlat A E) (hD : localHomKFlat A D) (hT : localHomKFlat A T)

local notation "LQ" => derivedBimoduleRestriction A C D C E (DGFunctor.id C) F
local notation "RR" => derivedBimoduleRestriction A D T E T F (DGFunctor.id T)

/-- 指定K-flatモデル上の一致を後二つの全導来変数へ持ち上げる。 -/
lemma secondMiddleRestrictionAssociatorPaths_eq :
    secondMiddleRestrictionAssociatorLeftPath A B C D E T F hE hD hT =
      secondMiddleRestrictionAssociatorRightPath A B C D E T F hD hT := by
  apply rightKFlatDerivedNatTrans_ext A E T hT
  intro R
  apply rightKFlatDerivedNatTrans_ext A C E hE
  intro Q
  rw [secondMiddleRestrictionAssociatorLeftPath_app, secondMiddleRestrictionAssociatorRightPath_app]
  exact derivedBimoduleAssociator_secondMiddleRestriction_rightKFlat A B C D E T F hE hD hT Q R

/-- 任意の導来三因子で、第二中間圏の全導来比較は実際の全導来結合子と可換。 -/
lemma derivedBimoduleAssociator_secondMiddleRestriction
    (Q : DerivedBimoduleCategory A C E) (R : DerivedBimoduleCategory A E T) :
    whiskerRight ((derivedBimoduleComposeLeftRestrictionIso A B C E D F hE hD).inv.app Q)
        ((derivedBimoduleComposeFunctor A B D T hT).obj ((RR).obj R)) ≫
      whiskerLeft ((derivedBimoduleComposeFunctor A B C E hE).obj Q)
        ((derivedMiddleRestrictionNatTrans A B E D T F hT).app R) ≫
      (derivedBimoduleAssociator A B C E T hE hT Q R).hom =
    (derivedBimoduleAssociator A B C D T hD hT ((LQ).obj Q) ((RR).obj R)).hom ≫
      (derivedBimoduleComposeFunctor A B C T hT).map
        (((derivedMiddleRestrictionNatTrans A C E D T F hT).app R).app Q) := by
  have h := NatTrans.congr_app
    (NatTrans.congr_app (secondMiddleRestrictionAssociatorPaths_eq A B C D E T F hE hD hT) R) Q
  simpa only [secondMiddleRestrictionAssociatorLeftPath_app,
    secondMiddleRestrictionAssociatorRightPath_app] using h

end SerrePositivity.DifferentialGraded.BimoduleTensor
