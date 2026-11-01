module
public import SerrePositivity.DifferentialGraded.Tensor.Associator.Components
public import Mathlib.Data.ZMod.Basic

/-! # 結合比較の全次数自然変換と順逆の閉単位の受入監査 -/
@[expose] public section
noncomputable section
universe u v w z t
open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded
open SerrePositivity.DifferentialGraded.BimoduleTensor
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z) (F : Type t)
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [DGCategory A F]
  [Small.{u} B] [Small.{u} C] [Small.{u} E]

example (P : Bimodule A B C) (Q : Bimodule A C E) (R : Bimodule A E F) :
    BimoduleParamTrans A B F (𝟙_ (Complex A))
      (compose A B E F (compose A B C E P Q) R)
      (compose A B C F P (compose A C E F Q R)) := associatorHom A B C E F P Q R
example (P : Bimodule A B C) (Q : Bimodule A C E) (R : Bimodule A E F) :
    BimoduleParamTrans A B F (𝟙_ (Complex A))
      (compose A B C F P (compose A C E F Q R))
      (compose A B E F (compose A B C E P Q) R) := associatorInv A B C E F P Q R

example (P Q R : Bimodule (ZMod 2) PUnit.{1} PUnit.{1}) (f : PUnit.{1}) :
    (λ_ (𝟙_ (Complex (ZMod 2)))).inv ≫
      ((associatorHom (ZMod 2) PUnit.{1} PUnit.{1} PUnit.{1} PUnit.{1} P Q R).app f ⊗ₘ
        (associatorInv (ZMod 2) PUnit.{1} PUnit.{1} PUnit.{1} PUnit.{1} P Q R).app f) ≫
      eComp (Complex (ZMod 2))
        ((compose (ZMod 2) PUnit.{1} PUnit.{1} PUnit.{1}
          (compose (ZMod 2) PUnit.{1} PUnit.{1} PUnit.{1} P Q) R).rightAt f)
        ((compose (ZMod 2) PUnit.{1} PUnit.{1} PUnit.{1} P
          (compose (ZMod 2) PUnit.{1} PUnit.{1} PUnit.{1} Q R)).rightAt f)
        ((compose (ZMod 2) PUnit.{1} PUnit.{1} PUnit.{1}
          (compose (ZMod 2) PUnit.{1} PUnit.{1} PUnit.{1} P Q) R).rightAt f) =
      eId (Complex (ZMod 2))
        ((compose (ZMod 2) PUnit.{1} PUnit.{1} PUnit.{1}
          (compose (ZMod 2) PUnit.{1} PUnit.{1} PUnit.{1} P Q) R).rightAt f) :=
  associator_hom_inv_app (ZMod 2) PUnit.{1} PUnit.{1} PUnit.{1} PUnit.{1} P Q R f

#check associatorHom_π
#check associatorInv_π
#check associator_inv_hom_app

#print axioms SerrePositivity.DifferentialGraded.BimoduleParamTrans
#print axioms SerrePositivity.DifferentialGraded.Bimodule.closedFamily_naturality
#print axioms SerrePositivity.DifferentialGraded.Bimodule.closedFamilyTrans
#print axioms SerrePositivity.DifferentialGraded.Bimodule.closedFamilyTrans_app
#print axioms SerrePositivity.DifferentialGraded.moduleHom_iso_square_inv
#print axioms SerrePositivity.DifferentialGraded.moduleIso_closed_hom_inv
#print axioms SerrePositivity.DifferentialGraded.Bimodule.isoFamily_inv_naturality
#print axioms SerrePositivity.DifferentialGraded.Bimodule.isoFamilyHom
#print axioms SerrePositivity.DifferentialGraded.Bimodule.isoFamilyInv
#print axioms SerrePositivity.DifferentialGraded.Bimodule.isoFamilyHom_app
#print axioms SerrePositivity.DifferentialGraded.Bimodule.isoFamilyInv_app
#print axioms SerrePositivity.DifferentialGraded.Bimodule.isoFamily_hom_inv_app
#print axioms SerrePositivity.DifferentialGraded.Bimodule.isoFamily_inv_hom_app
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.associatorHom
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.associatorHom_app
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.associatorInv
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.associatorInv_app
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.associator_hom_inv_app
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.associator_inv_hom_app
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.associatorHom_π
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.associatorInv_π
