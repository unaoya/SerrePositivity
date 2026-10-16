module
public import SerrePositivity.DifferentialGraded.Quotient.PathEvaluationDifferential
public import SerrePositivity.DifferentialGraded.Quotient.InternalEvaluationPrefix
public import SerrePositivity.DifferentialGraded.Quotient.ErasureRowRecursion
public import SerrePositivity.DifferentialGraded.Quotient.ErasureOperator

/-! # 全path評価のHom微分とε消去作用素の整合性 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] {D : Type v} [DGCategory A D] [Small.{u} D]
  {S : Set D} {E : Type w} [DGCategory A E]

lemma pathEvaluationTail_internalEvaluation (C : ContractedFunctor A D S E)
    (b : S) (w : Word S) (x y : D) (p : ℤ)
    (f : Cochain (term A D w b.val y) (internalHom A D S b.val y) p) :
    pathEvaluationTail A C b w x y p
      (f.comp (internalEvaluation A C b.val y) (add_zero p)) =
    (prefixTailCochain A D b w x y p f).comp (internalEvaluation A C x y) (add_zero p) := by
  rw [pathEvaluationTail, tensorLeftHom_cochain_comp, tensorLeftHom_cochain_comp,
    Cochain.comp_assoc_of_third_is_zero_cochain, ← internalEvaluation_prefixPath,
    ← Cochain.comp_assoc_of_second_is_zero_cochain]
  rfl

lemma pathEvaluation_differential (C : ContractedFunctor A D S E) (w : Word S) (x y : D) :
    δ 0 1 (pathEvaluation A C w x y) =
      (eraseRow A D w x y).comp (internalEvaluation A C x y) (add_zero 1) := by
  induction w generalizing x with
  | nil => rw [pathEvaluation_nil, δ_ofHom, eraseRow_nil, Cochain.zero_comp]
  | cons b w ih =>
    rw [pathEvaluation_cons_differential, ih b.val, pathEvaluationTail_internalEvaluation,
      eraseRow_cons, Cochain.add_comp _ _ _ (add_zero 1),
      Cochain.comp_assoc_of_second_is_zero_cochain, internalEvaluation_precomp]

lemma internalEvaluation_differential (C : ContractedFunctor A D S E) (x y : D) :
    δ 0 1 (internalEvaluation A C x y) =
      (erasure A D S x y).comp (internalEvaluation A C x y) (add_zero 1) := by
  apply pathCochain_ext A D S x y 1
  intro w
  rw [← δ_ofHom_comp, internalEvaluation_precomp,
    ← Cochain.comp_assoc_of_first_is_zero_cochain, erasure_precomp]
  exact pathEvaluation_differential A C w x y

end SerrePositivity.DifferentialGraded.DGQuotient
