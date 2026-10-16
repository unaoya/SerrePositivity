module
public import SerrePositivity.DifferentialGraded.Quotient.PrependErasure
public import SerrePositivity.DifferentialGraded.Quotient.Differential
public import SerrePositivity.DifferentialGraded.Complexes.Composition

/-! # 最終Hom微分に関する先頭Hom作用

内部chain mapとε消去の基底Leibniz則を加えて、元のHomと最終path Homのtensorから
最終path Homへの実際のchain mapを構成する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory Limits Preadditive MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 空pathを左に置く合成の、最終微分についてのLeibniz則。 -/
lemma internalPrepend_total_d_apply (S : Set D) (x y z : D) (p q n : ℤ)
    (hn : p + q = n) (a : (homObject A D x y).X p) (b : (internalHom A D S y z).X q) :
    (quotientHom A D S x z).d n (n + 1)
      ((internalPrepend A D S x y z).f n
        (ιTensorObj (homObject A D x y) (internalHom A D S y z) p q n hn (a ⊗ₜ[A] b))) =
    (internalPrepend A D S x y z).f (n + 1)
      (ιTensorObj (homObject A D x y) (internalHom A D S y z) (p + 1) q (n + 1)
        (by omega) ((homObject A D x y).d p (p + 1) a ⊗ₜ[A] b)) +
    p.negOnePow • (internalPrepend A D S x y z).f (n + 1)
      (ιTensorObj (homObject A D x y) (internalHom A D S y z) p (q + 1) (n + 1)
        (by omega) (a ⊗ₜ[A] (quotientHom A D S y z).d q (q + 1) b)) := by
  have hi := ConcreteCategory.congr_hom ((internalPrepend A D S x y z).comm n (n + 1))
    (ιTensorObj (homObject A D x y) (internalHom A D S y z) p q n hn (a ⊗ₜ[A] b))
  change (internalHom A D S x z).d n (n + 1) (_ : (internalHom A D S x z).X n) =
    (internalPrepend A D S x y z).f (n + 1)
      ((homObject A D x y ⊗ internalHom A D S y z).d n (n + 1)
        (ιTensorObj (homObject A D x y) (internalHom A D S y z) p q n hn (a ⊗ₜ[A] b))) at hi
  have hd := SerrePositivity.cochainTensor_d_apply_ι
    (homObject A D x y) (internalHom A D S y z) p q n hn a b
  have hi' := hi.trans (congrArg (fun v :
      (homObject A D x y ⊗ internalHom A D S y z).X (n + 1) =>
    (internalPrepend A D S x y z).f (n + 1) v) hd)
  clear hi
  have hi := hi'
  rw [map_add, chain_units_smul] at hi
  rw [quotientHom_d, quotientHom_d]
  change (internalHom A D S x z).d n (n + 1)
      ((internalPrepend A D S x y z).f n
        (ιTensorObj (homObject A D x y) (internalHom A D S y z) p q n hn (a ⊗ₜ[A] b))) +
      (erasure A D S x z).v n (n + 1) rfl
        ((internalPrepend A D S x y z).f n
          (ιTensorObj (homObject A D x y) (internalHom A D S y z) p q n hn (a ⊗ₜ[A] b))) =
    (internalPrepend A D S x y z).f (n + 1)
      (ιTensorObj (homObject A D x y) (internalHom A D S y z) (p + 1) q (n + 1)
        (by omega) ((homObject A D x y).d p (p + 1) a ⊗ₜ[A] b)) +
    p.negOnePow • (internalPrepend A D S x y z).f (n + 1)
      (ιTensorObj (homObject A D x y) (internalHom A D S y z) p (q + 1) (n + 1)
        (by omega) (a ⊗ₜ[A] ((internalHom A D S y z).d q (q + 1) b +
          (erasure A D S y z).v q (q + 1) rfl b)))
  exact (congrArg₂ (· + ·) hi (internalPrepend_erasure_apply A D S x y z p q n hn a b)).trans (by
    simp only [TensorProduct.tmul_add, map_add, smul_add]
    abel)

/-- 元のHomは最終Hom複体へ先頭から作用する。これは最終微分に関するchain map。 -/
def quotientPrepend (S : Set D) (x y z : D) :
    homObject A D x y ⊗ quotientHom A D S y z ⟶ quotientHom A D S x z :=
  tensorLift (fun i j n h =>
    ιTensorObj (homObject A D x y) (internalHom A D S y z) i j n h ≫
      (internalPrepend A D S x y z).f n) (fun i j => by
        apply ModuleCat.hom_ext
        apply TensorProduct.ext'
        intro a b
        exact internalPrepend_total_d_apply A D S x y z i j (i + j) rfl a b)

lemma quotientPrepend_ι (S : Set D) (x y z : D) (i j n : ℤ) (hn : i + j = n) :
    ιTensorObj (homObject A D x y) (quotientHom A D S y z) i j n hn ≫
      (quotientPrepend A D S x y z).f n =
    ιTensorObj (homObject A D x y) (internalHom A D S y z) i j n hn ≫
      (internalPrepend A D S x y z).f n :=
  ι_tensorLift _ _ i j n hn

end SerrePositivity.DifferentialGraded.DGQuotient
