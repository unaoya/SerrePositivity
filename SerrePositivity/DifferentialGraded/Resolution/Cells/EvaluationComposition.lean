module
public import SerrePositivity.DifferentialGraded.Resolution.Cells.Evaluation
public import SerrePositivity.DifferentialGraded.Resolution.Cells.InternalEvaluationComposition

/-! # 最終Homの評価chain mapの合成保存 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z
namespace SerrePositivity.DifferentialGraded.DGCellAttachment.Family.PrimitiveData
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D] {I : Type w} [Small.{u} I]
  {C : Family A D I} {E : Type z} [DGCategory A E] {F : DGFunctor A D E}
variable (P : PrimitiveData A D I C E F)

lemma attachedEvaluation_composition (x y z : D) :
    C.attachedComposition A D I x y z ≫ P.attachedEvaluation x z =
    (P.attachedEvaluation x y ⊗ₘ P.attachedEvaluation y z) ≫
      eComp (Complex A) (F.obj x) (F.obj y) (F.obj z) := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply mapBifunctor.hom_ext
  intro p q hn
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro a b
  change (P.attachedEvaluation x z).f n
      ((C.attachedComposition A D I x y z).f n
        (ιTensorObj (C.attachedHom A D I x y) (C.attachedHom A D I y z) p q n hn (a ⊗ₜ[A] b))) =
    (eComp (Complex A) (F.obj x) (F.obj y) (F.obj z)).f n
      ((P.attachedEvaluation x y ⊗ₘ P.attachedEvaluation y z).f n
        (ιTensorObj (C.attachedHom A D I x y) (C.attachedHom A D I y z) p q n hn (a ⊗ₜ[A] b)))
  rw [Family.attachedComposition_apply, tensorMap_apply]
  simp only [attachedEvaluation_f]
  have h := congrArg (fun f : Cochain (C.internalHom A D I x y ⊗ C.internalHom A D I y z)
      (homObject A E (F.obj x) (F.obj z)) 0 =>
    f.v n n (add_zero n)
      (ιTensorObj (C.internalHom A D I x y) (C.internalHom A D I y z) p q n hn (a ⊗ₜ[A] b)))
    (P.internalEvaluation_composition x y z)
  rw [cochain_ofHom_comp_apply, cochain_comp_ofHom_apply, tensorZeroCochain_apply] at h
  exact h

end SerrePositivity.DifferentialGraded.DGCellAttachment.Family.PrimitiveData
