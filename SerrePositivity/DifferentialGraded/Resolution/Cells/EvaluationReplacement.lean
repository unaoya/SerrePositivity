module
public import SerrePositivity.DifferentialGraded.Resolution.Cells.PathEvaluationDifferential
public import SerrePositivity.DifferentialGraded.Resolution.Cells.InternalEvaluationPrefix
public import SerrePositivity.DifferentialGraded.Resolution.Cells.BoundaryRowRecursion
public import SerrePositivity.DifferentialGraded.Resolution.Cells.BoundaryOperator

/-! # 全path評価のHom微分と指定境界置換作用素の整合性 -/
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

lemma pathEvaluationTail_internalEvaluation (b : I) (w : List I) (x y : D) (p : ℤ)
    (f : Cochain (C.term A D I w (C.target b) y) (C.internalHom A D I (C.target b) y) p) :
    P.pathEvaluationTail b w x y p
      (f.comp (P.internalEvaluation (C.target b) y) (add_zero p)) =
    (C.prefixTailCochain A D I b w x y p f).comp (P.internalEvaluation x y) (add_zero p) := by
  rw [pathEvaluationTail, tensorLeftHom_cochain_comp, tensorLeftHom_cochain_comp,
    Cochain.comp_assoc_of_third_is_zero_cochain, ← internalEvaluation_prefixPath,
    ← Cochain.comp_assoc_of_second_is_zero_cochain]
  rfl

lemma pathEvaluation_differential (w : List I) (x y : D) :
    δ 0 1 (P.pathEvaluation w x y) =
      (C.replaceRow A D I w x y).comp (P.internalEvaluation x y) (add_zero 1) := by
  induction w generalizing x with
  | nil => rw [pathEvaluation_nil, δ_ofHom, Family.replaceRow_nil, Cochain.zero_comp]
  | cons b w ih =>
    rw [pathEvaluation_cons_differential, ih (C.target b), pathEvaluationTail_internalEvaluation,
      Family.replaceRow_cons, Cochain.add_comp _ _ _ (add_zero 1),
      Cochain.comp_assoc_of_second_is_zero_cochain, internalEvaluation_precomp]

lemma internalEvaluation_differential (x y : D) :
    δ 0 1 (P.internalEvaluation x y) =
      (C.replacement A D I x y).comp (P.internalEvaluation x y) (add_zero 1) := by
  apply C.pathCochain_ext A D I x y 1
  intro w
  rw [← δ_ofHom_comp, internalEvaluation_precomp,
    ← Cochain.comp_assoc_of_first_is_zero_cochain, Family.replacement_precomp]
  exact P.pathEvaluation_differential w x y

end SerrePositivity.DifferentialGraded.DGCellAttachment.Family.PrimitiveData
