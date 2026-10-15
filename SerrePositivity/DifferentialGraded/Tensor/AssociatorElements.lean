module
public import SerrePositivity.DifferentialGraded.Tensor.AssociatorCochainExt
public import SerrePositivity.DifferentialGraded.Tensor.BimoduleElements
public import SerrePositivity.DifferentialGraded.Complexes.MapEvaluation

/-! # bimodule結合比較の斉次三重生成元での計算 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z t
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory MonoidalCategory Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z) (F : Type t)
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [DGCategory A F]
  [Small.{u} B] [Small.{u} C] [Small.{u} E]

/-- 左括弧の合成の斉次三重生成元。 -/
def associatorLeftElement (P : Bimodule A B C) (Q : Bimodule A C E) (R : Bimodule A E F)
    (b : B) (c : C) (e : E) (f : F) {k r s i n : ℤ}
    (t : (R.value e f).X k) (q : (Q.value c e).X r) (v : (P.value b c).X s)
    (hi : r + s = i) (hn : k + i = n) :
    ((compose A B E F (compose A B C E P Q) R).value b f).X n :=
  BalancedTensor.element A E (R.rightAt f) ((compose A B C E P Q).leftAt b) e t
    (BalancedTensor.element A C (Q.rightAt e) (P.leftAt b) c q v hi) hn

/-- 右括弧の合成の斉次三重生成元。 -/
def associatorRightElement (P : Bimodule A B C) (Q : Bimodule A C E) (R : Bimodule A E F)
    (b : B) (c : C) (e : E) (f : F) {k r s l n : ℤ}
    (t : (R.value e f).X k) (q : (Q.value c e).X r) (v : (P.value b c).X s)
    (hl : k + r = l) (hn : l + s = n) :
    ((compose A B C F P (compose A C E F Q R)).value b f).X n :=
  BalancedTensor.element A C ((compose A C E F Q R).rightAt f) (P.leftAt b) c
    (BalancedTensor.element A E (R.rightAt f) (Q.leftAt c) e t q hl) v hn

lemma associatorLeftElement_eq_ι (P : Bimodule A B C) (Q : Bimodule A C E)
    (R : Bimodule A E F) (b : B) (c : C) (e : E) (f : F) {k r s i n : ℤ}
    (t : (R.value e f).X k) (q : (Q.value c e).X r) (v : (P.value b c).X s)
    (hi : r + s = i) (hn : k + i = n) :
    associatorLeftElement A B C E F P Q R b c e f t q v hi hn =
    (associatorLeftι A B C E F P Q R b c e f).f n
      (ιTensorObj (R.value e f) (Q.value c e ⊗ P.value b c) k i n hn
        (t ⊗ₜ[A] ιTensorObj (Q.value c e) (P.value b c) r s i hi (q ⊗ₜ[A] v))) := by
  have h := whiskerLeft_apply (R.value e f)
    (BalancedTensor.ι A C (Q.rightAt e) (P.leftAt b) c) k i n hn t
      (ιTensorObj ((Q.rightAt e).obj (op c)) ((P.leftAt b).obj c) r s i hi (q ⊗ₜ[A] v))
  exact (congrArg (fun z =>
    (BalancedTensor.ι A E (R.rightAt f) ((compose A B C E P Q).leftAt b) e).f n z) h).symm

lemma associatorRightElement_eq_ι (P : Bimodule A B C) (Q : Bimodule A C E)
    (R : Bimodule A E F) (b : B) (c : C) (e : E) (f : F) {k r s i l n : ℤ}
    (t : (R.value e f).X k) (q : (Q.value c e).X r) (v : (P.value b c).X s)
    (hi : r + s = i) (hl : k + r = l) (hn : k + i = n) :
    associatorRightElement A B C E F P Q R b c e f t q v hl (by omega) =
    (associatorRightι A B C E F P Q R b c e f).f n
      (ιTensorObj (R.value e f) (Q.value c e ⊗ P.value b c) k i n hn
        (t ⊗ₜ[A] ιTensorObj (Q.value c e) (P.value b c) r s i hi (q ⊗ₜ[A] v))) := by
  have h := BalancedTensor.Fubini.tripleElement_rightι A C E
    (Q := Q) (R := R.rightAt f) (N := P.leftAt b)
    (𝟙 (BalancedTensor.Fubini.rightObj A C E Q (R.rightAt f) (P.leftAt b)))
    c e t q v hi hl hn
  exact h.symm

/-- 結合比較はR,Q,Pの順の三重生成元を符号なしで送る。 -/
lemma associatorValueIso_hom_element (P : Bimodule A B C) (Q : Bimodule A C E)
    (R : Bimodule A E F) (b : B) (c : C) (e : E) (f : F) {k r s i l n : ℤ}
    (t : (R.value e f).X k) (q : (Q.value c e).X r) (v : (P.value b c).X s)
    (hi : r + s = i) (hl : k + r = l) (hn : k + i = n) :
    (associatorValueIso A B C E F P Q R b f).hom.f n
      (associatorLeftElement A B C E F P Q R b c e f t q v hi hn) =
    associatorRightElement A B C E F P Q R b c e f t q v hl (by omega) := by
  have hpoint := chain_comp_apply_of_eq
    (associatorLeftι A B C E F P Q R b c e f)
    (associatorValueIso A B C E F P Q R b f).hom
    (associatorRightι A B C E F P Q R b c e f)
    (associatorLeftι_hom A B C E F P Q R b c e f) n
    (ιTensorObj (R.value e f) (Q.value c e ⊗ P.value b c) k i n hn
      (t ⊗ₜ[A] ιTensorObj (Q.value c e) (P.value b c) r s i hi (q ⊗ₜ[A] v)))
  calc
    _ = (associatorValueIso A B C E F P Q R b f).hom.f n
        ((associatorLeftι A B C E F P Q R b c e f).f n
          (ιTensorObj (R.value e f) (Q.value c e ⊗ P.value b c) k i n hn
            (t ⊗ₜ[A] ιTensorObj (Q.value c e) (P.value b c) r s i hi (q ⊗ₜ[A] v)))) :=
      congrArg (fun z => (associatorValueIso A B C E F P Q R b f).hom.f n z)
        (associatorLeftElement_eq_ι A B C E F P Q R b c e f t q v hi hn)
    _ = (associatorRightι A B C E F P Q R b c e f).f n
        (ιTensorObj (R.value e f) (Q.value c e ⊗ P.value b c) k i n hn
          (t ⊗ₜ[A] ιTensorObj (Q.value c e) (P.value b c) r s i hi (q ⊗ₜ[A] v))) :=
      hpoint
    _ = _ := (associatorRightElement_eq_ι A B C E F P Q R b c e f t q v hi hl hn).symm

end SerrePositivity.DifferentialGraded.BimoduleTensor
