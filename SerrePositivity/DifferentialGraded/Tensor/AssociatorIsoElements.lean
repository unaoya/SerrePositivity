module
public import SerrePositivity.DifferentialGraded.Tensor.AssociatorValueEvaluation
public import SerrePositivity.DifferentialGraded.Tensor.AssociatorValueHom

/-! # 閉零bimodule結合同型の値を三重生成元で評価する -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z t
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory HomologicalComplex
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z) (F : Type t)
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [DGCategory A F]
  [Small.{u} B] [Small.{u} C] [Small.{u} E]

lemma associatorIso_hom_value_element (P : Bimodule A B C) (Q : Bimodule A C E)
    (R : Bimodule A E F) (b : B) (c : C) (e : E) (d : F) {k r s i l n : ℤ}
    (τ : (R.value e d).X k) (q : (Q.value c e).X r) (v : (P.value b c).X s)
    (hi : r + s = i) (hl : k + r = l) (hn : k + i = n) :
    ((BimoduleCategory.valueEvaluation A B F b d).map
      (associatorIso A B C E F P Q R).hom).f n
      (associatorLeftElement A B C E F P Q R b c e d τ q v hi hn) =
    associatorRightElement A B C E F P Q R b c e d τ q v hl (by omega) := by
  have h := (associatorIso_hom_value_eval A B C E F P Q R b d).trans
    (associatorValueHom_eq A B C E F P Q R b d).symm
  have he := congrArg (fun a : (compose A B E F (compose A B C E P Q) R).value b d ⟶
      (compose A B C F P (compose A C E F Q R)).value b d =>
    a.f n (associatorLeftElement A B C E F P Q R b c e d τ q v hi hn)) h
  exact he.trans (associatorValueComponent_element A B C E F P Q R b c e d τ q v hi hl hn)

end SerrePositivity.DifferentialGraded.BimoduleTensor
