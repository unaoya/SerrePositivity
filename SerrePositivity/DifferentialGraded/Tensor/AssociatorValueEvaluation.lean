module
public import SerrePositivity.DifferentialGraded.Tensor.AssociatorIso
public import SerrePositivity.DifferentialGraded.Bimodule.LeftEvaluation

/-! # 閉零bimodule結合同型の値の複体への評価 -/
@[expose] public section
noncomputable section
universe u v w z t
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z) (F : Type t)
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [DGCategory A F]
  [Small.{u} B] [Small.{u} C] [Small.{u} E]

@[simp]
lemma associatorIso_hom_value_eval (P : Bimodule A B C) (Q : Bimodule A C E)
    (R : Bimodule A E F) (b : B) (d : F) :
    (BimoduleCategory.valueEvaluation A B F b d).map (associatorIso A B C E F P Q R).hom =
      (associatorValueIso A B C E F P Q R b d).hom :=
  associatorRightModuleIso_hom_eval A B C E F P Q R b d

@[simp]
lemma associatorIso_inv_value_eval (P : Bimodule A B C) (Q : Bimodule A C E)
    (R : Bimodule A E F) (b : B) (d : F) :
    (BimoduleCategory.valueEvaluation A B F b d).map (associatorIso A B C E F P Q R).inv =
      (associatorValueIso A B C E F P Q R b d).inv :=
  associatorRightModuleIso_inv_eval A B C E F P Q R b d

end SerrePositivity.DifferentialGraded.BimoduleTensor
