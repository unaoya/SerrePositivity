module
public import SerrePositivity.DifferentialGraded.Derived.BimoduleTensorNaturality
public import SerrePositivity.DifferentialGraded.Derived.BimoduleTensorTriangle
public import Mathlib.Data.ZMod.Basic

/-! # 導来結合比較の固定因子自然性と三角整合性の受入監査 -/
@[expose] public section
noncomputable section
universe u v w z t
open CategoryTheory CategoryTheory.Functor
open SerrePositivity.DifferentialGraded
open SerrePositivity.DifferentialGraded.BimoduleTensor
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z) (F : Type t)
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [DGCategory A F]
  [Small.{u} B] [Small.{u} C] [Small.{u} E]

example {Q Q' : BimoduleCategory A C E}
    {R R' : BimoduleCategory A E F}
    (hQ : Bimodule.rightRelativeKFlat A C E (BimoduleCategory.underlying A C E Q))
    (hQ' : Bimodule.rightRelativeKFlat A C E (BimoduleCategory.underlying A C E Q'))
    (hR : Bimodule.rightRelativeKFlat A E F (BimoduleCategory.underlying A E F R))
    (hR' : Bimodule.rightRelativeKFlat A E F (BimoduleCategory.underlying A E F R'))
    (g : Q ⟶ Q') (h : R ⟶ R') :
    (whiskerRight (derivedComposeWithMap A B C E hQ hQ' g) (derivedComposeWith A B E F R hR) ≫
        whiskerLeft (derivedComposeWith A B C E Q' hQ')
          (derivedComposeWithMap A B E F hR hR' h)) ≫
      (derivedAssociatorIso A B C E F Q' R' hQ' hR').hom =
    (derivedAssociatorIso A B C E F Q R hQ hR).hom ≫
      derivedComposeWithMap A B C F
        (Bimodule.rightRelativeKFlat_compose A C E F
          (BimoduleCategory.underlying A C E Q) (BimoduleCategory.underlying A E F R) hQ hR)
        (Bimodule.rightRelativeKFlat_compose A C E F
          (BimoduleCategory.underlying A C E Q') (BimoduleCategory.underlying A E F R') hQ' hR')
        (composeMap A C E F g h) :=
  derivedAssociatorIso_naturality A B C E F hQ hQ' hR hR' g h

example (Q : BimoduleCategory A C E)
    (hQ : Bimodule.rightRelativeKFlat A C E (BimoduleCategory.underlying A C E Q)) :
    (derivedAssociatorIso A B C C E
        (BimoduleCategory.of A C C (Bimodule.diagonal A C)) Q
        (Bimodule.diagonal_rightRelativeKFlat A C) hQ).hom ≫
      derivedComposeWithMap A B C E
        (Bimodule.rightRelativeKFlat_compose A C C E (Bimodule.diagonal A C)
          (BimoduleCategory.underlying A C E Q) (Bimodule.diagonal_rightRelativeKFlat A C) hQ)
        hQ (leftBimoduleUnitIso A C E (BimoduleCategory.underlying A C E Q)).hom =
    whiskerRight (derivedRightUnitIso A B C).hom (derivedComposeWith A B C E Q hQ) ≫
      (Functor.leftUnitor (derivedComposeWith A B C E Q hQ)).hom :=
  derivedTriangle A B C E Q hQ

example (Q : BimoduleCategory (ZMod 2) PUnit.{1} PUnit.{1})
    (hQ : Bimodule.rightRelativeKFlat (ZMod 2) PUnit.{1} PUnit.{1} (BimoduleCategory.underlying
      (ZMod 2) PUnit.{1} PUnit.{1} Q)) :
    (derivedAssociatorIso (ZMod 2) PUnit.{1} PUnit.{1} PUnit.{1} PUnit.{1}
        (BimoduleCategory.of (ZMod 2) PUnit.{1} PUnit.{1} (Bimodule.diagonal (ZMod 2) PUnit.{1})) Q
        (Bimodule.diagonal_rightRelativeKFlat (ZMod 2) PUnit.{1}) hQ).hom ≫
      derivedComposeWithMap (ZMod 2) PUnit.{1} PUnit.{1} PUnit.{1}
        (Bimodule.rightRelativeKFlat_compose (ZMod 2) PUnit.{1} PUnit.{1} PUnit.{1}
      (Bimodule.diagonal (ZMod 2) PUnit.{1})
          (BimoduleCategory.underlying (ZMod 2) PUnit.{1} PUnit.{1} Q)
      (Bimodule.diagonal_rightRelativeKFlat (ZMod 2) PUnit.{1}) hQ)
        hQ (leftBimoduleUnitIso (ZMod 2) PUnit.{1} PUnit.{1} (BimoduleCategory.underlying (ZMod 2)
      PUnit.{1} PUnit.{1} Q)).hom =
    whiskerRight (derivedRightUnitIso (ZMod 2) PUnit.{1} PUnit.{1}).hom (derivedComposeWith (ZMod
      2) PUnit.{1} PUnit.{1} PUnit.{1} Q hQ) ≫
      (Functor.leftUnitor (derivedComposeWith (ZMod 2) PUnit.{1} PUnit.{1} PUnit.{1} Q hQ)).hom :=
  derivedTriangle (ZMod 2) PUnit.{1} PUnit.{1} PUnit.{1} Q hQ

#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.derivedComposeWith_map_base
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.derivedComposeWithMap_base_app
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.derivedRightUnitIso_base_app
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.derivedAssociatorIso_base_app
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.derivedAssociatorIso_naturality
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.derivedTriangle
