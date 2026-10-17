module
public import SerrePositivity.DifferentialGraded.Derived.AssociatorRightRestrictionFamilies

/-! # 全導来三因子に対する結合子と外側右制限のcoherence -/
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
  (T : Type s) [DGCategory A T] [Small.{u} T] (F : DGFunctor A D B)
  (hE : localHomKFlat A E) (hT : localHomKFlat A T)

local notation "RI" => derivedBimoduleRestriction A D C B C F (DGFunctor.id C)
local notation "RO" => derivedBimoduleRestriction A D T B T F (DGFunctor.id T)

/-- 指定K-flatモデル上の一致から全後二因子に自然な経路の一致を得る。 -/
lemma rightRestrictionAssociatorPaths_eq :
    rightRestrictionAssociatorLeftPath A B D C E T F hE hT =
      rightRestrictionAssociatorRightPath A B D C E T F hE hT := by
  apply rightKFlatDerivedNatTrans_ext A E T hT
  intro R
  apply rightKFlatDerivedNatTrans_ext A C E hE
  intro Q
  rw [rightRestrictionAssociatorLeftPath_app, rightRestrictionAssociatorRightPath_app]
  exact derivedBimoduleAssociator_rightRestriction_rightKFlat A B D C E T F hE hT Q R

/-- 任意の導来三因子について、外側右制限が実際の全導来結合子を保つ。 -/
lemma derivedBimoduleAssociator_rightRestriction
    (Q : DerivedBimoduleCategory A C E) (R : DerivedBimoduleCategory A E T) :
    whiskerLeft RI (derivedBimoduleAssociator A D C E T hE hT Q R).hom ≫
      (derivedBimoduleComposeRightRestrictionIso A B D C T F hT).hom.app
        (((derivedBimoduleComposeFunctor A C E T hT).obj R).obj Q) =
    whiskerRight ((derivedBimoduleComposeRightRestrictionIso A B D C E F hE).hom.app Q)
        ((derivedBimoduleComposeFunctor A D E T hT).obj R) ≫
      whiskerLeft ((derivedBimoduleComposeFunctor A B C E hE).obj Q)
        ((derivedBimoduleComposeRightRestrictionIso A B D E T F hT).hom.app R) ≫
      whiskerRight (derivedBimoduleAssociator A B C E T hE hT Q R).hom RO := by
  have h := NatTrans.congr_app
    (NatTrans.congr_app (rightRestrictionAssociatorPaths_eq A B D C E T F hE hT) R) Q
  simpa only [rightRestrictionAssociatorLeftPath_app,
    rightRestrictionAssociatorRightPath_app] using h

end SerrePositivity.DifferentialGraded.BimoduleTensor
