module
public import SerrePositivity.DifferentialGraded.Tensor.QuadElements
public import SerrePositivity.DifferentialGraded.Tensor.AssociatorDegreeExt

/-! # 四重生成元による完全左反復tensorからのcochainの外延性 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z t x
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z)
  (F : Type t) (G : Type x)
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [DGCategory A F] [DGCategory A G]
  [Small.{u} B] [Small.{u} C] [Small.{u} E] [Small.{u} F]

lemma quadLeft_cochain_element_ext (P : Bimodule A B C) (Q : Bimodule A C E)
    (R : Bimodule A E F) (S : Bimodule A F G) (b : B) (g : G)
    {T : Complex A} {p : ℤ}
    (u v : Cochain ((compose A B F G (compose A B E F (compose A B C E P Q) R) S).value b g) T p)
    (heq : ∀ (c : C) (e : E) (f : F) (a k r s i m n t : ℤ)
      (hi : r + s = i) (hm : k + i = m) (hn : a + m = n) (ht : n + p = t)
      (σ : (S.value f g).X a) (τ : (R.value e f).X k)
      (q : (Q.value c e).X r) (w : (P.value b c).X s),
      u.v n t ht (quadLeftElement A B C E F G P Q R S b c e f g σ τ q w hi hm hn) =
        v.v n t ht (quadLeftElement A B C E F G P Q R S b c e f g σ τ q w hi hm hn)) : u = v := by
  apply BalancedTensor.cochain_element_ext A F (S.rightAt g)
    ((compose A B E F (compose A B C E P Q) R).leftAt b)
  intro f a m n t hn ht σ z
  let K := (compose A B E F (compose A B C E P Q) R).value b f
  let L : K.X m →ₗ[A] T.X t := (u.v n t ht).hom.comp
    (((BalancedTensor.ι A F (S.rightAt g)
      ((compose A B E F (compose A B C E P Q) R).leftAt b) f).f n).hom.comp
        ((ιTensorObj (S.value f g) K a m n hn).hom.comp (TensorProduct.mk A _ _ σ)))
  let H : K.X m →ₗ[A] T.X t := (v.v n t ht).hom.comp
    (((BalancedTensor.ι A F (S.rightAt g)
      ((compose A B E F (compose A B C E P Q) R).leftAt b) f).f n).hom.comp
        ((ιTensorObj (S.value f g) K a m n hn).hom.comp (TensorProduct.mk A _ _ σ)))
  have hh : ModuleCat.ofHom L = ModuleCat.ofHom H := by
    apply associatorLeft_degree_element_ext A B C E F P Q R b f
    intro c e k r s i hi hm τ q w
    exact heq c e f a k r s i m n t hi hm hn ht σ τ q w
  exact congrArg (fun j => j z) hh

end SerrePositivity.DifferentialGraded.BimoduleTensor
