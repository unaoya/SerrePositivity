module
public import SerrePositivity.DifferentialGraded.Tensor.AssociatorGenerators
public import SerrePositivity.DifferentialGraded.Tensor.DegreeElementsExt

/-! # 実際の反復bimodule tensorを源とする全次数cochainの外延性 -/
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

/-- 微分との可換性を仮定せず、左括弧の反復tensorからのcochainを三重生成元で判定する。 -/
lemma associatorLeft_cochain_element_ext (P : Bimodule A B C) (Q : Bimodule A C E)
    (R : Bimodule A E F) (b : B) (f : F) {T : Complex A} {p : ℤ}
    (g h : Cochain ((compose A B E F (compose A B C E P Q) R).value b f) T p)
    (heq : ∀ (c : C) (e : E) (k r s i m n : ℤ)
      (hi : r + s = i) (hm : k + i = m) (hn : m + p = n)
      (t : (R.value e f).X k) (q : (Q.value c e).X r) (v : (P.value b c).X s),
      g.v m n hn (BalancedTensor.element A E (R.rightAt f)
        ((compose A B C E P Q).leftAt b) e t
        (BalancedTensor.element A C (Q.rightAt e) (P.leftAt b) c q v hi) hm) =
      h.v m n hn (BalancedTensor.element A E (R.rightAt f)
        ((compose A B C E P Q).leftAt b) e t
        (BalancedTensor.element A C (Q.rightAt e) (P.leftAt b) c q v hi) hm)) : g = h := by
  apply BalancedTensor.cochain_element_ext A E (R.rightAt f) ((compose A B C E P Q).leftAt b)
  intro e k i m n hm hn t z
  let K := BalancedTensor.obj A C (Q.rightAt e) (P.leftAt b)
  let L : K.X i →ₗ[A] T.X n :=
    (g.v m n hn).hom.comp
      (((BalancedTensor.ι A E (R.rightAt f) ((compose A B C E P Q).leftAt b) e).f m).hom.comp
        ((ιTensorObj (R.value e f) K k i m hm).hom.comp
          (TensorProduct.mk A ((R.value e f).X k) (K.X i) t)))
  let H : K.X i →ₗ[A] T.X n :=
    (h.v m n hn).hom.comp
      (((BalancedTensor.ι A E (R.rightAt f) ((compose A B C E P Q).leftAt b) e).f m).hom.comp
        ((ιTensorObj (R.value e f) K k i m hm).hom.comp
          (TensorProduct.mk A ((R.value e f).X k) (K.X i) t)))
  have ht : ModuleCat.ofHom L = ModuleCat.ofHom H := by
    apply BalancedTensor.degree_element_ext A C (Q.rightAt e) (P.leftAt b)
    intro c r s hi q v
    exact heq c e k r s i m n hi hm hn t q v
  exact congrArg (fun j => j z) ht

end SerrePositivity.DifferentialGraded.BimoduleTensor
