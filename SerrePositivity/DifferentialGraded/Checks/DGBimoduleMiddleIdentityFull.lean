module
public import SerrePositivity.DifferentialGraded.Derived.BimoduleMiddleIdentityFamily
public import SerrePositivity.DifferentialGraded.Derived.BimoduleMiddleIdentityFull
public import SerrePositivity.DifferentialGraded.Derived.BimoduleMiddleComparisonComputation
public import SerrePositivity.DifferentialGraded.Derived.BimoduleLiftIso
public import Mathlib.Data.ZMod.Basic

/-! # 恒等比較の全導来化と指定モデル計算の公理監査 -/
@[expose] public section
noncomputable section
universe u v w z
open CategoryTheory
open SerrePositivity.DifferentialGraded
open SerrePositivity.DifferentialGraded.BimoduleTensor
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (D : Type w) [DGCategory A D] [Small.{u} D]
  (L : Type z) [DGCategory A L] [Small.{u} L] (hL : localHomKFlat A L)

example (Q : DerivedBimoduleCategory A D L) (P : DerivedBimoduleCategory A B D) :
    ((derivedMiddleRestrictionNatTrans A B D D L (DGFunctor.id D) hL).app Q).app P =
      ((derivedMiddleIdentityIso A B D L hL).hom.app Q).app P := by
  rw [derivedMiddleRestrictionNatTrans_functor_id]

example (X : Type v) (Y : Type w) (Z : Type z)
    [DGCategory (ZMod 2) X] [DGCategory (ZMod 2) Y] [DGCategory (ZMod 2) Z]
    [Small.{0} X] [Small.{0} Y] [Small.{0} Z] (hZ : localHomKFlat (ZMod 2) Z) :
    derivedMiddleRestrictionNatTrans (ZMod 2) X Y Y Z (DGFunctor.id Y) hZ =
      (derivedMiddleIdentityIso (ZMod 2) X Y Z hZ).hom :=
  derivedMiddleRestrictionNatTrans_functor_id (ZMod 2) X Y Z hZ

#print axioms BimoduleTensor.middleClosedIdentityIso
#print axioms BimoduleTensor.middleClosedIdentityIso_hom_app
#print axioms BimoduleTensor.middleIdentitySourceFamilyIso
#print axioms BimoduleTensor.derivedMiddleRestrictionCanonicalFamily_functor_id
#print axioms BimoduleTensor.middleIdentitySourceLiftIso
#print axioms BimoduleTensor.derivedMiddleRestrictionCanonicalLocalized_functor_id
#print axioms BimoduleTensor.middleIdentityKFlatIso
#print axioms BimoduleTensor.middleDerivedKFlatComparison_functor_id
#print axioms BimoduleTensor.middleIdentityLocalizedIso
#print axioms BimoduleTensor.middleRightKFlatLocalizedComparison_functor_id
#print axioms BimoduleTensor.middleFullIdentityIso
#print axioms BimoduleTensor.middleFullDerivedComparison_functor_id
#print axioms BimoduleTensor.derivedMiddleIdentityIso
#print axioms BimoduleTensor.derivedMiddleRestrictionNatTrans_functor_id
#print axioms BimoduleTensor.derivedMiddleIdentityIso_transport
#print axioms BimoduleTensor.middleLocalizedRestrictionComparison
#print axioms BimoduleTensor.derivedMiddleRestrictionNatTrans_conjugate
#print axioms BimoduleTensor.derivedMiddleRestrictionNatTrans_precomp_rightKFlat
#print axioms BimoduleTensor.middleLocalizedRestrictionComparison_eq_lift
#print axioms BimoduleTensor.middleLocalizedRestrictionComparison_app
#print axioms BimoduleTensor.derivedMiddleRestrictionNatTrans_app_rightKFlat
#print axioms BimoduleTensor.middleRightKFlatComparison_eq_first_lift
#print axioms BimoduleTensor.derivedMiddleRestrictionNatTrans_app_base
#print axioms bimoduleDerivedIsoOfPrecomp
#print axioms bimoduleDerivedIsoOfPrecomp_hom_app
#print axioms bimoduleDerivedIsoOfPrecomp_inv_app
