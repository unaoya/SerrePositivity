module
public import SerrePositivity.DifferentialGraded.Derived.BimoduleTensorFunctor
public import Mathlib.Data.ZMod.Basic

/-! # U12eの標準局所化と固定K-flat因子による導来合成の受入監査 -/
@[expose] public section
noncomputable section
universe u v w z y y'
open CategoryTheory
open SerrePositivity.DifferentialGraded
open SerrePositivity.DifferentialGraded.BimoduleTensor
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z)
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [Small.{u} B]

example : Category.{max (u + 1) v w} (DerivedBimoduleCategory A B C) := inferInstance

example {T : Type y} [Category.{y'} T] (G : BimoduleCategory A B C ⥤ T)
    (hG : (BimoduleCategory.quasiIso A B C).IsInvertedBy G) :
    bimoduleToDerived A B C ⋙ bimoduleDerivedLift A B C G hG = G :=
  bimoduleDerivedLift_fac A B C G hG

variable [Small.{u} C]
-- Eのsmall性と射影モデル構造は不要。
example (Q : BimoduleCategory A C E)
    (hQ : Bimodule.rightRelativeKFlat A C E (BimoduleCategory.underlying A C E Q)) :
    DerivedBimoduleCategory A B C ⥤ DerivedBimoduleCategory A B E :=
  derivedComposeWith A B C E Q hQ

example (Q : BimoduleCategory A C E)
    (hQ : Bimodule.rightRelativeKFlat A C E (BimoduleCategory.underlying A C E Q)) :
    bimoduleToDerived A B C ⋙ derivedComposeWith A B C E Q hQ =
      composeWith A B C E Q ⋙ bimoduleToDerived A B E :=
  derivedComposeWith_fac A B C E Q hQ

example (Q : BimoduleCategory A C E)
    (hQ : Bimodule.rightRelativeKFlat A C E (BimoduleCategory.underlying A C E Q))
    (G : DerivedBimoduleCategory A B C ⥤ DerivedBimoduleCategory A B E)
    (hG : bimoduleToDerived A B C ⋙ G = composeWith A B C E Q ⋙ bimoduleToDerived A B E) :
    G = derivedComposeWith A B C E Q hQ := derivedComposeWith_unique A B C E Q hQ G hG

example : RightKFlatBimoduleCategory A C E ⥤
    (DerivedBimoduleCategory A B C ⥤ DerivedBimoduleCategory A B E) :=
  derivedComposeWithFunctor A B C E

example (Q : RightKFlatBimoduleCategory A C E) :
    (derivedComposeWithFunctor A B C E).map (𝟙 Q) =
      𝟙 ((derivedComposeWithFunctor A B C E).obj Q) :=
  (derivedComposeWithFunctor A B C E).map_id Q

example {Q Q' Q'' : RightKFlatBimoduleCategory A C E} (g : Q ⟶ Q') (h : Q' ⟶ Q'') :
    (derivedComposeWithFunctor A B C E).map (g ≫ h) =
      (derivedComposeWithFunctor A B C E).map g ≫ (derivedComposeWithFunctor A B C E).map h :=
  (derivedComposeWithFunctor A B C E).map_comp g h

example : DerivedBimoduleCategory (ZMod 2) PUnit.{1} PUnit.{1} ⥤
    DerivedBimoduleCategory (ZMod 2) PUnit.{1} PUnit.{1} :=
  derivedComposeWith (ZMod 2) PUnit.{1} PUnit.{1} PUnit.{1}
    (BimoduleCategory.of (ZMod 2) PUnit.{1} PUnit.{1} (Bimodule.diagonal (ZMod 2) PUnit.{1}))
    (Bimodule.diagonal_rightRelativeKFlat (ZMod 2) PUnit.{1})

#print axioms SerrePositivity.DifferentialGraded.DerivedBimoduleCategory
#print axioms SerrePositivity.DifferentialGraded.bimoduleToDerived
#print axioms SerrePositivity.DifferentialGraded.bimoduleToDerived_inverts
#print axioms SerrePositivity.DifferentialGraded.bimoduleDerivedIso
#print axioms SerrePositivity.DifferentialGraded.bimoduleDerivedLift
#print axioms SerrePositivity.DifferentialGraded.bimoduleDerivedLift_fac
#print axioms SerrePositivity.DifferentialGraded.bimoduleDerivedLift_unique
#print axioms SerrePositivity.DifferentialGraded.bimoduleDerivedNatTrans_ext
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.composeWith
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.composeWith_preserves_quasiIso
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.composeWith_toDerived_inverts
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.derivedComposeWith
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.derivedComposeWith_fac
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.derivedComposeWith_lifting
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.derivedComposeWithComputation
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.derivedComposeWith_unique
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.composeWithMap
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.composeWithMap_id
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.composeWithMap_comp
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.derivedComposeWithMap
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.derivedComposeWithMap_app
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.derivedComposeWithMap_id
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.derivedComposeWithMap_comp
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.RightKFlatBimoduleCategory
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.derivedComposeWithFunctor
