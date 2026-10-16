module
public import SerrePositivity.DifferentialGraded.Tensor.AssociatorBimodule
public import Mathlib.Data.ZMod.Basic

/-! # bimodule結合比較の両作用自然性・右加群同型の受入監査 -/
@[expose] public section
noncomputable section
universe u v w z t
open CategoryTheory Opposite
open SerrePositivity.DifferentialGraded
open SerrePositivity.DifferentialGraded.BimoduleTensor
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z) (F : Type t)
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [DGCategory A F]
  [Small.{u} B] [Small.{u} C] [Small.{u} E]

example (P : Bimodule A B C) (Q : Bimodule A C E) (R : Bimodule A E F) (f : F) :
    ForgetEnrichment.of (Complex A) ((compose A B E F (compose A B C E P Q) R).rightAt f) ≅
      ForgetEnrichment.of (Complex A) ((compose A B C F P (compose A C E F Q R)).rightAt f) :=
  associatorRightModuleIso A B C E F P Q R f

example (P : Bimodule A B C) (Q : Bimodule A C E) (R : Bimodule A E F) (b : B) (f : F) :
    (moduleEvaluation A B b).map (associatorRightModuleIso A B C E F P Q R f).hom =
      (associatorValueIso A B C E F P Q R b f).hom :=
  associatorRightModuleIso_hom_eval A B C E F P Q R b f

example (P Q R : Bimodule (ZMod 2) PUnit.{1} PUnit.{1}) (b c e f : PUnit.{1})
    (g : GradedHom (ZMod 2) f f (-1)) (t : (R.value e f).X 1)
    (q : (Q.value c e).X 0) (v : (P.value b c).X 0) :
    associatorValueComponent (ZMod 2) PUnit.{1} PUnit.{1} PUnit.{1} PUnit.{1} P Q R b f 0
      ((associatorLeftCochain (ZMod 2) PUnit.{1} PUnit.{1} PUnit.{1} PUnit.{1}
        P Q R b f f (-1) g).v 1 0 (by decide)
        (associatorLeftElement (ZMod 2) PUnit.{1} PUnit.{1} PUnit.{1} PUnit.{1}
          P Q R b c e f (i := 0) (n := 1) t q v (by decide) (by decide))) =
    (associatorRightCochain (ZMod 2) PUnit.{1} PUnit.{1} PUnit.{1} PUnit.{1}
      P Q R b f f (-1) g).v 1 0 (by decide)
      (associatorValueComponent (ZMod 2) PUnit.{1} PUnit.{1} PUnit.{1} PUnit.{1}
        P Q R b f 1
        (associatorLeftElement (ZMod 2) PUnit.{1} PUnit.{1} PUnit.{1} PUnit.{1}
          P Q R b c e f (i := 0) (n := 1) t q v (by decide) (by decide))) :=
  associatorComponent_leftCochain_compatibility (ZMod 2)
    PUnit.{1} PUnit.{1} PUnit.{1} PUnit.{1} P Q R b c e f f
      (by decide) (by decide) (by decide) g t q v

#check associatorValue_left_naturality
#check associatorValue_right_naturality_actual
#check associatorRightModuleIso_naturality

#print axioms SerrePositivity.DifferentialGraded.chainMapOfComponentFunctions
#print axioms SerrePositivity.DifferentialGraded.chainMapOfComponentFunctions_apply
#print axioms SerrePositivity.DifferentialGraded.chainMapOfComponentFunctions_eq
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.associatorLeftCochain_element_map
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.associatorValueComponent
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.associatorValueComponent_eq
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.associatorValueComponent_element
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.associatorLeftComponent_transport
#print axioms
  SerrePositivity.DifferentialGraded.BimoduleTensor.associatorComponent_leftCochain_compatibility
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.associatorValueHom
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.associatorValueHom_apply
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.associatorValueHom_eq
#print axioms
  SerrePositivity.DifferentialGraded.BimoduleTensor.associatorValueHom_leftAction_compatibility
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.associatorValueHom_left_naturality
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.associatorValue_left_naturality
#print axioms
  SerrePositivity.DifferentialGraded.BimoduleTensor.associatorComponent_rightCochain_compatibility
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.associatorValueHom_right_naturality
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.associatorValue_right_naturality
#print axioms
  SerrePositivity.DifferentialGraded.BimoduleTensor.associatorValue_right_naturality_actual
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.associatorRightModuleIso
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.associatorRightModuleIso_hom_eval
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.associatorRightModuleIso_inv_eval
#print axioms
  SerrePositivity.DifferentialGraded.BimoduleTensor.associatorRightModuleIso_hom_component
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.associatorRightModuleIso_naturality
