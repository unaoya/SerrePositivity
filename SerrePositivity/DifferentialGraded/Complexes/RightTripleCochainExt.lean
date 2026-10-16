module
public import SerrePositivity.DifferentialGraded.Complexes.AssociatorCochainFactors

/-! # 右括弧三重tensor上の任意次数cochainの判定 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable {A : Type u} [CommRing A]

lemma rightTripleCochain_ext {P Q R T : Complex A} {p : ℤ}
    (f g : Cochain (P ⊗ (Q ⊗ R)) T p)
    (h : ∀ (i j k a n : ℤ) (ha : i + (j + k) = a) (hn : a + p = n)
      (x : P.X i) (y : Q.X j) (z : R.X k),
      f.v a n hn (ιTensorObj P (Q ⊗ R) i (j + k) a ha
        (x ⊗ₜ[A] ιTensorObj Q R j k (j + k) rfl (y ⊗ₜ[A] z))) =
      g.v a n hn (ιTensorObj P (Q ⊗ R) i (j + k) a ha
        (x ⊗ₜ[A] ιTensorObj Q R j k (j + k) rfl (y ⊗ₜ[A] z)))) : f = g := by
  apply Cochain.ext
  intro a n hn
  apply (cancel_epi ((α_ P Q R).hom.f a)).1
  apply SerrePositivity.cochainTensorTriple_hom_ext P Q R a
  intro i j k ha
  apply ModuleCat.hom_ext
  apply TensorProduct.ext_threefold
  intro x y z
  change f.v a n hn ((α_ P Q R).hom.f a
      (ιTensorObj (P ⊗ Q) R (i + j) k a ha
        (ιTensorObj P Q i j (i + j) rfl (x ⊗ₜ[A] y) ⊗ₜ[A] z))) =
    g.v a n hn ((α_ P Q R).hom.f a
      (ιTensorObj (P ⊗ Q) R (i + j) k a ha
        (ιTensorObj P Q i j (i + j) rfl (x ⊗ₜ[A] y) ⊗ₜ[A] z)))
  simpa only [associator_apply] using h i j k a n (by omega) hn x y z

lemma rightTripleCochain_ext₀ {P Q R T : Complex A}
    (f g : Cochain (P ⊗ (Q ⊗ R)) T 0)
    (h : ∀ (i j k n : ℤ) (hn : i + (j + k) = n)
      (x : P.X i) (y : Q.X j) (z : R.X k),
      f.v n n (add_zero n) (ιTensorObj P (Q ⊗ R) i (j + k) n hn
        (x ⊗ₜ[A] ιTensorObj Q R j k (j + k) rfl (y ⊗ₜ[A] z))) =
      g.v n n (add_zero n) (ιTensorObj P (Q ⊗ R) i (j + k) n hn
        (x ⊗ₜ[A] ιTensorObj Q R j k (j + k) rfl (y ⊗ₜ[A] z)))) : f = g := by
  apply Cochain.ext₀
  intro n
  apply (cancel_epi ((α_ P Q R).hom.f n)).1
  apply SerrePositivity.cochainTensorTriple_hom_ext P Q R n
  intro i j k hn
  apply ModuleCat.hom_ext
  apply TensorProduct.ext_threefold
  intro x y z
  change f.v n n (add_zero n) ((α_ P Q R).hom.f n
      (ιTensorObj (P ⊗ Q) R (i + j) k n hn
        (ιTensorObj P Q i j (i + j) rfl (x ⊗ₜ[A] y) ⊗ₜ[A] z))) =
    g.v n n (add_zero n) ((α_ P Q R).hom.f n
      (ιTensorObj (P ⊗ Q) R (i + j) k n hn
        (ιTensorObj P Q i j (i + j) rfl (x ⊗ₜ[A] y) ⊗ₜ[A] z)))
  simpa only [associator_apply] using h i j k n (by omega) x y z

end SerrePositivity.DifferentialGraded
