module
public import SerrePositivity.DifferentialGraded.Quotient.InternalEvaluation
public import SerrePositivity.DifferentialGraded.Quotient.PathEvaluationAppend
public import SerrePositivity.DifferentialGraded.Quotient.InternalComposition
public import SerrePositivity.DifferentialGraded.Quotient.TensorTwoPathCochainExt

/-! # 全path直和の評価は内部合成を保つ -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] {D : Type v} [DGCategory A D] [Small.{u} D]
  {S : Set D} {E : Type w} [DGCategory A E]

lemma internalEvaluation_composition (C : ContractedFunctor A D S E) (x y z : D) :
    (Cochain.ofHom (internalComposition A D S x y z)).comp (internalEvaluation A C x z)
      (zero_add 0) =
    (tensorZeroCochain (internalEvaluation A C x y) (internalEvaluation A C y z)).comp
      (Cochain.ofHom (eComp (Complex A) (C.toDGFunctor.obj x)
        (C.toDGFunctor.obj y) (C.toDGFunctor.obj z))) (zero_add 0) := by
  apply tensorTwoPathCochain_ext A D S x y z 0
  intro w v
  rw [← Cochain.comp_assoc_of_first_is_zero_cochain, ← Cochain.ofHom_comp,
    internalComposition_ι, Cochain.ofHom_comp, Cochain.comp_assoc_of_first_is_zero_cochain,
    internalEvaluation_precomp,
    ← Cochain.comp_assoc_of_first_is_zero_cochain, tensorZeroCochain_precomp,
    internalEvaluation_precomp, internalEvaluation_precomp]
  exact pathEvaluation_append A C w v x y z

end SerrePositivity.DifferentialGraded.DGQuotient
