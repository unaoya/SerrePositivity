module
public import SerrePositivity.DifferentialGraded.Tensor.Associator.Components
public import Mathlib.Data.ZMod.Basic

/-! # 反復相対tensorの両括弧における全次数作用写像とcochainの監査 -/
@[expose] public section
noncomputable section
universe u v w z t
open CategoryTheory Opposite HomologicalComplex CochainComplex HomComplex
open SerrePositivity.DifferentialGraded
open SerrePositivity.DifferentialGraded.BimoduleTensor
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z) (F : Type t)
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [DGCategory A F]
  [Small.{u} B] [Small.{u} C] [Small.{u} E]

example (P : Bimodule A B C) (Q : Bimodule A C E) (R : Bimodule A E F)
    (b : B) (f f' : F) (p : ℤ) (g : GradedHom A f f' p) :
    (associatorLeftMap A B C E F P Q R b f f').f p g =
      associatorLeftCochain A B C E F P Q R b f f' p g :=
  associatorLeftMap_apply A B C E F P Q R b f f' p g
example (P : Bimodule A B C) (Q : Bimodule A C E) (R : Bimodule A E F)
    (b b' : Bᵒᵖ) (f : F) (p : ℤ) (g : GradedHom A b b' p) :
    (associatorRightBMap A B C E F P Q R b b' f).f p g =
      associatorRightBCochain A B C E F P Q R b b' f p g :=
  associatorRightBMap_apply A B C E F P Q R b b' f p g
example (P Q R : Bimodule (ZMod 2) PUnit.{1} PUnit.{1})
    (g : GradedHom (ZMod 2) (PUnit.unit : PUnit.{1}) PUnit.unit (-1)) :
    (associatorRightMap (ZMod 2) PUnit.{1} PUnit.{1} PUnit.{1} PUnit.{1}
      P Q R PUnit.unit PUnit.unit PUnit.unit).f (-1) g =
      associatorRightCochain (ZMod 2) PUnit.{1} PUnit.{1} PUnit.{1} PUnit.{1}
        P Q R PUnit.unit PUnit.unit PUnit.unit (-1) g :=
  associatorRightMap_apply (ZMod 2) PUnit.{1} PUnit.{1} PUnit.{1} PUnit.{1}
    P Q R PUnit.unit PUnit.unit PUnit.unit (-1) g

#print axioms associatorLeftCochain
#print axioms associatorRightCochain
#print axioms associatorLeftCochain_apply
#print axioms associatorRightCochain_apply
#print axioms associatorLeftMap
#print axioms associatorRightMap
#print axioms associatorLeftMap_apply
#print axioms associatorRightMap_apply
#print axioms associatorLeftBMap
#print axioms associatorRightBMap
#print axioms associatorLeftBCochain
#print axioms associatorRightBCochain
#print axioms associatorLeftBMap_apply
#print axioms associatorRightBMap_apply
#print axioms associatorLeftBCochain_apply
#print axioms associatorRightBCochain_apply

#print axioms associatorLeftCochain_element
#print axioms associatorRightCochain_element
#print axioms associatorLeftBCochain_element
#print axioms associatorRightBCochain_element
