module
public import SerrePositivity.DifferentialGraded.Resolution.Cells.InternalEvaluation
public import SerrePositivity.DifferentialGraded.Resolution.Cells.PathEvaluationAppend
public import SerrePositivity.DifferentialGraded.Resolution.Cells.InternalComposition
public import SerrePositivity.DifferentialGraded.Resolution.Cells.TensorTwoPathCochainExt

/-! # 全path直和の評価は内部合成を保つ -/
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

lemma internalEvaluation_composition (x y z : D) :
    (Cochain.ofHom (C.internalComposition A D I x y z)).comp (P.internalEvaluation x z)
      (zero_add 0) =
    (tensorZeroCochain (P.internalEvaluation x y) (P.internalEvaluation y z)).comp
      (Cochain.ofHom (eComp (Complex A) (F.obj x)
        (F.obj y) (F.obj z))) (zero_add 0) := by
  apply C.tensorTwoPathCochain_ext A D I x y z 0
  intro w v
  rw [← Cochain.comp_assoc_of_first_is_zero_cochain, ← Cochain.ofHom_comp,
    Family.internalComposition_inclusion, Cochain.ofHom_comp,
    Cochain.comp_assoc_of_first_is_zero_cochain,
    internalEvaluation_precomp,
    ← Cochain.comp_assoc_of_first_is_zero_cochain, tensorZeroCochain_precomp,
    internalEvaluation_precomp, internalEvaluation_precomp]
  exact P.pathEvaluation_append w v x y z

end SerrePositivity.DifferentialGraded.DGCellAttachment.Family.PrimitiveData
