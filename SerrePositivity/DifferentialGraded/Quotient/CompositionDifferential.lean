module
public import SerrePositivity.DifferentialGraded.Quotient.CompositionErasure
public import SerrePositivity.DifferentialGraded.Quotient.Differential
public import SerrePositivity.DifferentialGraded.Complexes.Composition

/-! # 全pathの最終Hom微分に関する合成 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory Limits Preadditive MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 全消去Leibniz則の斉次成分。右の消去項の符号は左の次数p。 -/
lemma internalComposition_erasure_apply (S : Set D) (x y z : D) (p q n : ℤ)
    (hn : p + q = n) (a : (internalHom A D S x y).X p) (b : (internalHom A D S y z).X q) :
    (erasure A D S x z).v n (n + 1) rfl
      ((internalComposition A D S x y z).f n
        (ιTensorObj (internalHom A D S x y) (internalHom A D S y z) p q n hn (a ⊗ₜ[A] b))) =
    (internalComposition A D S x y z).f (n + 1)
      (ιTensorObj (internalHom A D S x y) (internalHom A D S y z) (p + 1) q (n + 1)
        (by omega) ((erasure A D S x y).v p (p + 1) rfl a ⊗ₜ[A] b)) +
    p.negOnePow • (internalComposition A D S x y z).f (n + 1)
      (ιTensorObj (internalHom A D S x y) (internalHom A D S y z) p (q + 1) (n + 1)
        (by omega) (a ⊗ₜ[A] (erasure A D S y z).v q (q + 1) rfl b)) := by
  have h := congrArg (fun f : Cochain
      (internalHom A D S x y ⊗ internalHom A D S y z) (internalHom A D S x z) 1 =>
    f.v n (n + 1) rfl
      (ιTensorObj (internalHom A D S x y) (internalHom A D S y z) p q n hn (a ⊗ₜ[A] b)))
    (internalComposition_erasure A D S x y z)
  simp only [Cochain.add_v, ModuleCat.hom_add, LinearMap.add_apply] at h
  rw [cochain_ofHom_comp_apply, cochain_comp_ofHom_apply, cochain_comp_ofHom_apply,
    tensorRightHom_apply, tensorLeftHom_apply, chain_units_smul] at h
  simpa only [one_mul] using h

/-- 最終Homの全微分についてのLeibniz則。 -/
lemma internalComposition_total_d_apply (S : Set D) (x y z : D) (p q n : ℤ)
    (hn : p + q = n) (a : (internalHom A D S x y).X p) (b : (internalHom A D S y z).X q) :
    (quotientHom A D S x z).d n (n + 1)
      ((internalComposition A D S x y z).f n
        (ιTensorObj (internalHom A D S x y) (internalHom A D S y z) p q n hn (a ⊗ₜ[A] b))) =
    (internalComposition A D S x y z).f (n + 1)
      (ιTensorObj (internalHom A D S x y) (internalHom A D S y z) (p + 1) q (n + 1)
        (by omega) ((quotientHom A D S x y).d p (p + 1) a ⊗ₜ[A] b)) +
    p.negOnePow • (internalComposition A D S x y z).f (n + 1)
      (ιTensorObj (internalHom A D S x y) (internalHom A D S y z) p (q + 1) (n + 1)
        (by omega) (a ⊗ₜ[A] (quotientHom A D S y z).d q (q + 1) b)) := by
  have hi := ConcreteCategory.congr_hom ((internalComposition A D S x y z).comm n (n + 1))
    (ιTensorObj (internalHom A D S x y) (internalHom A D S y z) p q n hn (a ⊗ₜ[A] b))
  change (internalHom A D S x z).d n (n + 1) (_ : (internalHom A D S x z).X n) =
    (internalComposition A D S x y z).f (n + 1)
      ((internalHom A D S x y ⊗ internalHom A D S y z).d n (n + 1)
        (ιTensorObj (internalHom A D S x y) (internalHom A D S y z) p q n hn (a ⊗ₜ[A] b))) at hi
  have hd := SerrePositivity.cochainTensor_d_apply_ι
    (internalHom A D S x y) (internalHom A D S y z) p q n hn a b
  have hi' := hi.trans (congrArg (fun v :
      (internalHom A D S x y ⊗ internalHom A D S y z).X (n + 1) =>
    (internalComposition A D S x y z).f (n + 1) v) hd)
  clear hi
  have hi := hi'
  rw [map_add, chain_units_smul] at hi
  rw [quotientHom_d, quotientHom_d, quotientHom_d]
  change (internalHom A D S x z).d n (n + 1)
      ((internalComposition A D S x y z).f n
        (ιTensorObj (internalHom A D S x y) (internalHom A D S y z) p q n hn (a ⊗ₜ[A] b))) +
      (erasure A D S x z).v n (n + 1) rfl
        ((internalComposition A D S x y z).f n
          (ιTensorObj (internalHom A D S x y) (internalHom A D S y z) p q n hn (a ⊗ₜ[A] b))) =
    (internalComposition A D S x y z).f (n + 1)
      (ιTensorObj (internalHom A D S x y) (internalHom A D S y z) (p + 1) q (n + 1)
        (by omega) (((internalHom A D S x y).d p (p + 1) a +
          (erasure A D S x y).v p (p + 1) rfl a) ⊗ₜ[A] b)) +
    p.negOnePow • (internalComposition A D S x y z).f (n + 1)
      (ιTensorObj (internalHom A D S x y) (internalHom A D S y z) p (q + 1) (n + 1)
        (by omega) (a ⊗ₜ[A] ((internalHom A D S y z).d q (q + 1) b +
          (erasure A D S y z).v q (q + 1) rfl b)))
  exact (congrArg₂ (· + ·) hi
    (internalComposition_erasure_apply A D S x y z p q n hn a b)).trans (by
    simp only [TensorProduct.add_tmul, TensorProduct.tmul_add, map_add, smul_add]
    abel)

/-- 全pathの最終Hom複体間の合成。最終微分に関する実際のchain map。 -/
def quotientComposition (S : Set D) (x y z : D) :
    quotientHom A D S x y ⊗ quotientHom A D S y z ⟶ quotientHom A D S x z :=
  tensorLift (fun i j n h =>
    ιTensorObj (internalHom A D S x y) (internalHom A D S y z) i j n h ≫
      (internalComposition A D S x y z).f n) (fun i j => by
        apply ModuleCat.hom_ext
        apply TensorProduct.ext'
        intro a b
        exact internalComposition_total_d_apply A D S x y z i j (i + j) rfl a b)

lemma quotientComposition_ι (S : Set D) (x y z : D) (i j n : ℤ) (hn : i + j = n) :
    ιTensorObj (quotientHom A D S x y) (quotientHom A D S y z) i j n hn ≫
      (quotientComposition A D S x y z).f n =
    ιTensorObj (internalHom A D S x y) (internalHom A D S y z) i j n hn ≫
      (internalComposition A D S x y z).f n :=
  ι_tensorLift _ _ i j n hn

end SerrePositivity.DifferentialGraded.DGQuotient
