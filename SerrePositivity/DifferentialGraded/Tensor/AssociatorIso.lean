module
public import SerrePositivity.DifferentialGraded.Tensor.AssociatorTransforms
public import SerrePositivity.DifferentialGraded.Bimodule.Isomorphism

/-! # 全Hom自然な閉零bimodule圏での結合同型 -/
@[expose] public section
noncomputable section
universe u v w z t
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory MonoidalCategory
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z) (F : Type t)
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [DGCategory A F]
  [Small.{u} B] [Small.{u} C] [Small.{u} E]

/-- 全Hom自然な閉零射の圏におけるbimodule合成の結合同型。 -/
def associatorIso (P : Bimodule A B C) (Q : Bimodule A C E) (R : Bimodule A E F) :
    BimoduleCategory.of A B F (compose A B E F (compose A B C E P Q) R) ≅
      BimoduleCategory.of A B F (compose A B C F P (compose A C E F Q R)) :=
  BimoduleCategory.isoOfFamily A B F (associatorRightModuleIso A B C E F P Q R)
    (associatorRightModuleIso_naturality A B C E F P Q R)

@[simp]
lemma associatorIso_hom_eval (P : Bimodule A B C) (Q : Bimodule A C E)
    (R : Bimodule A E F) (f : F) :
    (BimoduleCategory.evaluation A B F f).map (associatorIso A B C E F P Q R).hom =
      (associatorRightModuleIso A B C E F P Q R f).hom := rfl

@[simp]
lemma associatorIso_inv_eval (P : Bimodule A B C) (Q : Bimodule A C E)
    (R : Bimodule A E F) (f : F) :
    (BimoduleCategory.evaluation A B F f).map (associatorIso A B C E F P Q R).inv =
      (associatorRightModuleIso A B C E F P Q R f).inv := rfl

lemma associatorIso_hom_trans (P : Bimodule A B C) (Q : Bimodule A C E)
    (R : Bimodule A E F) :
    (BimoduleCategory.homEquiv A B F _ _ (associatorIso A B C E F P Q R).hom) =
      associatorHom A B C E F P Q R := rfl

lemma associatorIso_inv_trans (P : Bimodule A B C) (Q : Bimodule A C E)
    (R : Bimodule A E F) :
    (BimoduleCategory.homEquiv A B F _ _ (associatorIso A B C E F P Q R).inv) =
      associatorInv A B C E F P Q R := rfl

end SerrePositivity.DifferentialGraded.BimoduleTensor
