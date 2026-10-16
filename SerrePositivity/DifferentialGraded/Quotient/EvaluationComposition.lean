module
public import SerrePositivity.DifferentialGraded.Quotient.Evaluation
public import SerrePositivity.DifferentialGraded.Quotient.InternalEvaluationComposition

/-! # 最終Homの評価chain mapの合成保存 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] {D : Type v} [DGCategory A D] [Small.{u} D]
  {S : Set D} {E : Type w} [DGCategory A E]

lemma quotientEvaluation_composition (C : ContractedFunctor A D S E) (x y z : D) :
    quotientComposition A D S x y z ≫ quotientEvaluation A C x z =
    (quotientEvaluation A C x y ⊗ₘ quotientEvaluation A C y z) ≫
      eComp (Complex A) (C.toDGFunctor.obj x) (C.toDGFunctor.obj y) (C.toDGFunctor.obj z) := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply mapBifunctor.hom_ext
  intro p q hn
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro a b
  change (quotientEvaluation A C x z).f n
      ((quotientComposition A D S x y z).f n
        (ιTensorObj (quotientHom A D S x y) (quotientHom A D S y z) p q n hn (a ⊗ₜ[A] b))) =
    (eComp (Complex A) (C.toDGFunctor.obj x) (C.toDGFunctor.obj y) (C.toDGFunctor.obj z)).f n
      ((quotientEvaluation A C x y ⊗ₘ quotientEvaluation A C y z).f n
        (ιTensorObj (quotientHom A D S x y) (quotientHom A D S y z) p q n hn (a ⊗ₜ[A] b)))
  rw [quotientComposition_apply, tensorMap_apply]
  simp only [quotientEvaluation_f]
  have h := congrArg (fun f : Cochain (internalHom A D S x y ⊗ internalHom A D S y z)
      (homObject A E (C.toDGFunctor.obj x) (C.toDGFunctor.obj z)) 0 =>
    f.v n n (add_zero n)
      (ιTensorObj (internalHom A D S x y) (internalHom A D S y z) p q n hn (a ⊗ₜ[A] b)))
    (internalEvaluation_composition A C x y z)
  rw [cochain_ofHom_comp_apply, cochain_comp_ofHom_apply, tensorZeroCochain_apply] at h
  exact h

end SerrePositivity.DifferentialGraded.DGQuotient
