module
public import SerrePositivity.DifferentialGraded.Derived.AssociatorLeftRestrictionCoherence
public import Mathlib.Data.ZMod.Basic

/-! # 全三因子に対する外側左制限と導来結合子のcoherenceの検査 -/
@[expose] public section
noncomputable section
universe v w z t s
open CategoryTheory CategoryTheory.Functor
open SerrePositivity.DifferentialGraded
open SerrePositivity.DifferentialGraded.BimoduleTensor

section CharacteristicTwo
variable (B : Type v) [DGCategory (ZMod 2) B] [Small.{0} B]
  (C : Type w) [DGCategory (ZMod 2) C] [Small.{0} C]
  (E : Type z) [DGCategory (ZMod 2) E] [Small.{0} E]
  (T : Type t) [DGCategory (ZMod 2) T] [Small.{0} T]
  (D : Type s) [DGCategory (ZMod 2) D] [Small.{0} D] (G : DGFunctor (ZMod 2) D T)
  (hE : localHomKFlat (ZMod 2) E) (hT : localHomKFlat (ZMod 2) T)
  (hD : localHomKFlat (ZMod 2) D)
  (Q : DerivedBimoduleCategory (ZMod 2) C E) (R : DerivedBimoduleCategory (ZMod 2) E T)
local notation "LE" => derivedBimoduleRestriction (ZMod 2) E D E T (DGFunctor.id E) G
local notation "L" => derivedBimoduleRestriction (ZMod 2) B D B T (DGFunctor.id B) G

-- Gの準同値性を仮定せず、後二因子も任意の導来対象とする。
theorem SerrePositivity.DifferentialGraded.Checks.associatorLeftRestriction_charTwo_component
    (P : DerivedBimoduleCategory (ZMod 2) B C) :
    ((derivedBimoduleAssociator (ZMod 2) B C E D hE hD Q ((LE).obj R)).hom ≫
      (derivedBimoduleComposeFunctor (ZMod 2) B C D hD).map
        (((derivedBimoduleComposeLeftRestrictionIso (ZMod 2) C E T D G hT hD).inv.app R).app Q) ≫
      (derivedBimoduleComposeLeftRestrictionIso (ZMod 2) B C T D G hT hD).inv.app
        (((derivedBimoduleComposeFunctor (ZMod 2) C E T hT).obj R).obj Q)).app P =
    (whiskerLeft ((derivedBimoduleComposeFunctor (ZMod 2) B C E hE).obj Q)
        ((derivedBimoduleComposeLeftRestrictionIso (ZMod 2) B E T D G hT hD).inv.app R) ≫
      whiskerRight (derivedBimoduleAssociator (ZMod 2) B C E T hE hT Q R).hom L).app P :=
  NatTrans.congr_app
    (derivedBimoduleAssociator_leftRestriction (ZMod 2) B C E T D G hE hT hD Q R) P
end CharacteristicTwo

#check derivedBimoduleAssociator_leftRestriction
#print axioms leftRestrictionAssociatorSource
#print axioms leftRestrictionAssociatorTarget
#print axioms leftRestrictionAssociatorAfterAssociator
#print axioms leftRestrictionAssociatorAfterInner
#print axioms leftRestrictionAssociatorRightMiddle
#print axioms leftRestrictionAssociatorLeftPath
#print axioms leftRestrictionAssociatorRightPath
#print axioms leftRestrictionAssociatorLeftPath_app
#print axioms leftRestrictionAssociatorRightPath_app
#print axioms leftRestrictionAssociatorPaths_eq
#print axioms derivedBimoduleAssociator_leftRestriction
#print axioms
  SerrePositivity.DifferentialGraded.Checks.associatorLeftRestriction_charTwo_component
