module
public import SerrePositivity.DifferentialGraded.Complexes.Braiding

/-! # 両方の中間和次数を指定するassociatorの成分式 -/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory HomologicalComplex
variable {A : Type u} [CommRing A]

lemma associator_apply_of_sums (P Q T : Complex A) (i j k l m n : ℤ)
    (hl : i + j = l) (hm : j + k = m) (hn : l + k = n)
    (x : P.X i) (y : Q.X j) (z : T.X k) :
    (α_ P Q T).hom.f n
      (ιTensorObj (P ⊗ Q) T l k n hn (ιTensorObj P Q i j l hl (x ⊗ₜ[A] y) ⊗ₜ[A] z)) =
    ιTensorObj P (Q ⊗ T) i m n (by omega)
      (x ⊗ₜ[A] ιTensorObj Q T j k m hm (y ⊗ₜ[A] z)) := by
  subst l m
  exact associator_apply P Q T i j k n hn x y z

end SerrePositivity.DifferentialGraded
