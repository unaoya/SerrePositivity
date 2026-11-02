module
public import SerrePositivity.DifferentialGraded.Tensor.Associator.Components
public import Mathlib.Data.ZMod.Basic

/-! # 全Hom自然な閉零bimodule圏と実際の結合同型の受入監査 -/
@[expose] public section
noncomputable section
universe u v w z t
open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded
open SerrePositivity.DifferentialGraded.BimoduleTensor
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w)
  [DGCategory A B] [DGCategory A C] [Small.{u} B]

example (M N : BimoduleCategory A B C) :
    (M ⟶ N) ≃ BimoduleParamTrans A B C (𝟙_ (Complex A))
      (BimoduleCategory.underlying A B C M) (BimoduleCategory.underlying A B C N) :=
  BimoduleCategory.homEquiv A B C M N
example (M N P : BimoduleCategory A B C) (a : M ⟶ N) (b : N ⟶ P) (c : C) :
    (BimoduleCategory.evaluation A B C c).map (a ≫ b) =
      (BimoduleCategory.evaluation A B C c).map a ≫
        (BimoduleCategory.evaluation A B C c).map b :=
  (BimoduleCategory.evaluation A B C c).map_comp a b

variable (E : Type z) (F : Type t) [DGCategory A E] [DGCategory A F]
  [Small.{u} C] [Small.{u} E]
example (P : Bimodule A B C) (Q : Bimodule A C E) (R : Bimodule A E F) :
    BimoduleCategory.of A B F (compose A B E F (compose A B C E P Q) R) ≅
      BimoduleCategory.of A B F (compose A B C F P (compose A C E F Q R)) :=
  associatorIso A B C E F P Q R
example (P : Bimodule A B C) (Q : Bimodule A C E) (R : Bimodule A E F) :
    BimoduleCategory.homEquiv A B F _ _ (associatorIso A B C E F P Q R).hom =
      associatorHom A B C E F P Q R := associatorIso_hom_trans A B C E F P Q R

example (P Q R : Bimodule (ZMod 2) PUnit.{1} PUnit.{1}) :
    (associatorIso (ZMod 2) PUnit.{1} PUnit.{1} PUnit.{1} PUnit.{1} P Q R).hom ≫
      (associatorIso (ZMod 2) PUnit.{1} PUnit.{1} PUnit.{1} PUnit.{1} P Q R).inv =
      𝟙 (BimoduleCategory.of (ZMod 2) PUnit.{1} PUnit.{1}
        (compose (ZMod 2) PUnit.{1} PUnit.{1} PUnit.{1}
          (compose (ZMod 2) PUnit.{1} PUnit.{1} PUnit.{1} P Q) R)) :=
  (associatorIso (ZMod 2) PUnit.{1} PUnit.{1} PUnit.{1} PUnit.{1} P Q R).hom_inv_id

#print axioms SerrePositivity.DifferentialGraded.Bimodule.closedFamily_naturality_converse
#print axioms SerrePositivity.DifferentialGraded.Bimodule.closedTransApp
#print axioms SerrePositivity.DifferentialGraded.Bimodule.closedTransApp_naturality
#print axioms SerrePositivity.DifferentialGraded.Bimodule.closedTransApp_closedFamilyTrans
#print axioms SerrePositivity.DifferentialGraded.Bimodule.closedFamilyTrans_closedTransApp
#print axioms SerrePositivity.DifferentialGraded.moduleHom_square_id
#print axioms SerrePositivity.DifferentialGraded.moduleHom_square_comp
#print axioms SerrePositivity.DifferentialGraded.Bimodule.ClosedMapFamily
#print axioms SerrePositivity.DifferentialGraded.Bimodule.closedMapFamilyEquiv
#print axioms SerrePositivity.DifferentialGraded.Bimodule.closedMapFamilyId
#print axioms SerrePositivity.DifferentialGraded.Bimodule.closedMapFamilyComp
#print axioms SerrePositivity.DifferentialGraded.BimoduleCategory
#print axioms SerrePositivity.DifferentialGraded.BimoduleCategory.of
#print axioms SerrePositivity.DifferentialGraded.BimoduleCategory.underlying
#print axioms SerrePositivity.DifferentialGraded.BimoduleCategory.category
#print axioms SerrePositivity.DifferentialGraded.BimoduleCategory.homEquiv
#print axioms SerrePositivity.DifferentialGraded.BimoduleCategory.evaluation
#print axioms SerrePositivity.DifferentialGraded.BimoduleCategory.hom_ext
#print axioms SerrePositivity.DifferentialGraded.BimoduleCategory.homEquiv_app
#print axioms SerrePositivity.DifferentialGraded.BimoduleCategory.homEquiv_comp_app
#print axioms SerrePositivity.DifferentialGraded.BimoduleCategory.isoOfFamily
#print axioms SerrePositivity.DifferentialGraded.BimoduleCategory.isoOfFamily_hom_eval
#print axioms SerrePositivity.DifferentialGraded.BimoduleCategory.isoOfFamily_inv_eval
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.associatorIso
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.associatorIso_hom_eval
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.associatorIso_inv_eval
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.associatorIso_hom_trans
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.associatorIso_inv_trans
