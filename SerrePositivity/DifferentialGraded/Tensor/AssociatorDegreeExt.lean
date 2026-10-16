module
public import SerrePositivity.DifferentialGraded.Tensor.AssociatorElements

/-! # 三重生成元による各次数の線形写像の外延性 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z t
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z) (F : Type t)
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [DGCategory A F]
  [Small.{u} B] [Small.{u} C] [Small.{u} E]

lemma associatorLeft_degree_element_ext (P : Bimodule A B C) (Q : Bimodule A C E)
    (R : Bimodule A E F) (b : B) (d : F) {n : ℤ} {T : ModuleCat.{u} A}
    (a h : ((compose A B E F (compose A B C E P Q) R).value b d).X n ⟶ T)
    (heq : ∀ (c : C) (e : E) (k r s i : ℤ) (hi : r + s = i) (hn : k + i = n)
      (τ : (R.value e d).X k) (q : (Q.value c e).X r) (v : (P.value b c).X s),
      a (associatorLeftElement A B C E F P Q R b c e d τ q v hi hn) =
        h (associatorLeftElement A B C E F P Q R b c e d τ q v hi hn)) : a = h := by
  apply BalancedTensor.degree_element_ext A E (R.rightAt d) ((compose A B C E P Q).leftAt b)
  intro e k i hn τ z
  let K := BalancedTensor.obj A C (Q.rightAt e) (P.leftAt b)
  let L : K.X i →ₗ[A] T := a.hom.comp
    (((BalancedTensor.ι A E (R.rightAt d) ((compose A B C E P Q).leftAt b) e).f n).hom.comp
      ((ιTensorObj (R.value e d) K k i n hn).hom.comp (TensorProduct.mk A _ _ τ)))
  let H : K.X i →ₗ[A] T := h.hom.comp
    (((BalancedTensor.ι A E (R.rightAt d) ((compose A B C E P Q).leftAt b) e).f n).hom.comp
      ((ιTensorObj (R.value e d) K k i n hn).hom.comp (TensorProduct.mk A _ _ τ)))
  have ht : ModuleCat.ofHom L = ModuleCat.ofHom H := by
    apply BalancedTensor.degree_element_ext A C (Q.rightAt e) (P.leftAt b)
    intro c r s hi q v
    exact heq c e k r s i hi hn τ q v
  exact congrArg (fun j => j z) ht

end SerrePositivity.DifferentialGraded.BimoduleTensor
