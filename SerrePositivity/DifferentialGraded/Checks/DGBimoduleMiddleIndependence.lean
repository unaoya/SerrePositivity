module
public import SerrePositivity.DifferentialGraded.Derived.BimoduleMiddleSemifreeIndependence
public import Mathlib.Data.ZMod.Basic

/-! # 中間圏導来比較の任意の制限後semifree解像度からの独立性の検査 -/
@[expose] public section
noncomputable section
universe u v w z t
open CategoryTheory
open SerrePositivity.DifferentialGraded
open SerrePositivity.DifferentialGraded.BimoduleTensor
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (C : Type w) [DGCategory A C] [Small.{u} C]
  (D : Type z) [DGCategory A D] [Small.{u} D]
  (E : Type t) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D C)
  (hE : localHomKFlat A E) (Q : RightKFlatBimoduleCategory A C E)
  (R S : BimoduleSemifreeResolution A D E
    ((BimoduleCategory.middleRightRestrictionFunctor A C D E F).obj Q.obj))

-- 選んだ二つのsemifree解像度に追加の増大squareを要求しない。
example (P : BimoduleCategory A B C) :
    derivedMiddleRestrictionComparison A B C D E F hE P Q
        (S.toRightKFlat A D E hE) S.π S.quasiIso =
      derivedMiddleRestrictionComparison A B C D E F hE P Q
        (R.toRightKFlat A D E hE) R.π R.quasiIso :=
  derivedMiddleRestrictionComparison_semifree_independent A B C D E F hE Q R S P

-- 自然変換の等式なので、前因子の全導来圏のすべての射に対する比較を含む。
example : derivedMiddleRestrictionComparisonLocalized A B C D E F hE Q
        (S.toRightKFlat A D E hE) S.π S.quasiIso =
      derivedMiddleRestrictionComparisonLocalized A B C D E F hE Q
        (R.toRightKFlat A D E hE) R.π R.quasiIso :=
  derivedMiddleRestrictionComparisonLocalized_semifree_independent A B C D E F hE Q R S

example : derivedMiddleRestrictionComparisonLocalized A B C D E F hE Q
        (R.toRightKFlat A D E hE) R.π R.quasiIso =
      derivedMiddleRestrictionCanonicalLocalized A B C D E F hE Q :=
  derivedMiddleRestrictionComparisonLocalized_semifree_eq_canonical A B C D E F hE Q R

example (X : Type v) (Y : Type w) (Z : Type z) (T : Type t)
    [DGCategory (ZMod 2) X] [DGCategory (ZMod 2) Y]
    [DGCategory (ZMod 2) Z] [DGCategory (ZMod 2) T]
    [Small.{0} X] [Small.{0} Y] [Small.{0} Z] [Small.{0} T]
    (F : DGFunctor (ZMod 2) Z Y) (hT : localHomKFlat (ZMod 2) T)
    (Q : RightKFlatBimoduleCategory (ZMod 2) Y T) :
    middleDerivedSourceLift (ZMod 2) X Y Z T F hT Q ⟶
      (derivedBimoduleComposeFunctor (ZMod 2) X Y T hT).obj
        ((bimoduleToDerived (ZMod 2) Y T).obj Q.obj) :=
  derivedMiddleRestrictionCanonicalLocalized (ZMod 2) X Y Z T F hT Q

namespace SerrePositivity.DifferentialGraded
#print axioms bimoduleDerived_map_eq_of_inverse_source_homotopy
#print axioms BimoduleTensor.derivedComposeWithMap_computation
#print axioms BimoduleTensor.derivedBimoduleComposeResolutionValueIso
#print axioms BimoduleTensor.derivedBimoduleComposeResolutionValueIso_change
#print axioms BimoduleTensor.derivedMiddleRestrictionComparison_eq_of_squares
#print axioms BimoduleTensor.derivedMiddleRestrictionComparison_eq_of_source_homotopy
#print axioms BimoduleSemifreeResolution.composeAfter_comparison_fac
#print axioms BimoduleSemifreeResolution.toRightKFlat
#print axioms BimoduleTensor.derivedMiddleRestrictionComparison_semifree_independent
#print axioms BimoduleTensor.derivedMiddleRestrictionComparisonFamily_semifree_independent
#print axioms BimoduleTensor.derivedMiddleRestrictionComparisonLocalized_semifree_independent
#print axioms BimoduleTensor.derivedMiddleRestrictionComparison_semifree_eq_canonical
#print axioms BimoduleTensor.derivedMiddleRestrictionCanonicalLocalized
#print axioms BimoduleTensor.derivedMiddleRestrictionComparisonLocalized_semifree_eq_canonical
end SerrePositivity.DifferentialGraded
