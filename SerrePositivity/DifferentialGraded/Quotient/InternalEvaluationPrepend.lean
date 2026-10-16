module
public import SerrePositivity.DifferentialGraded.Quotient.InternalEvaluation
public import SerrePositivity.DifferentialGraded.Quotient.PathEvaluationPrepend
public import SerrePositivity.DifferentialGraded.Quotient.PrependErasureRows
public import SerrePositivity.DifferentialGraded.Quotient.TensorPathCochainExt
public import SerrePositivity.DifferentialGraded.Complexes.TensorZeroCochainNaturality

/-! # 全path評価と元のHomによる先頭作用の整合性 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] {D : Type v} [DGCategory A D] [Small.{u} D]
  {S : Set D} {E : Type w} [DGCategory A E]

lemma internalEvaluation_prepend (C : ContractedFunctor A D S E) (x y z : D) :
    (Cochain.ofHom (internalPrepend A D S x y z)).comp (internalEvaluation A C x z) (zero_add 0) =
    (tensorZeroCochain (Cochain.ofHom (C.toDGFunctor.map x y)) (internalEvaluation A C y z)).comp
      (Cochain.ofHom (eComp (Complex A) (C.toDGFunctor.obj x)
        (C.toDGFunctor.obj y) (C.toDGFunctor.obj z))) (zero_add 0) := by
  apply tensorLeftPathCochain_ext A D S y z (homObject A D x y) 0
  intro w
  rw [← Cochain.comp_assoc_of_first_is_zero_cochain, ← Cochain.ofHom_comp,
    internalPrepend_ι, Cochain.ofHom_comp, Cochain.comp_assoc_of_first_is_zero_cochain,
    internalEvaluation_precomp]
  rw [← Cochain.comp_assoc_of_first_is_zero_cochain, tensorZeroCochain_precomp_right,
    internalEvaluation_precomp]
  exact pathEvaluation_prepend A C w x y z

end SerrePositivity.DifferentialGraded.DGQuotient
