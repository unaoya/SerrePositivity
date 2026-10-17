module
public import SerrePositivity.DifferentialGraded.Resolution.Cells.PrimitiveAction
public import SerrePositivity.DifferentialGraded.Resolution.Cells.PathEvaluationPrepend
public import SerrePositivity.DifferentialGraded.Resolution.Cells.BoundaryHead
public import SerrePositivity.DifferentialGraded.Complexes.TensorZeroCochainLeftMap

/-! # 原始元作用の微分と有限path先頭境界の評価 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z
namespace SerrePositivity.DifferentialGraded.DGCellAttachment.Family.PrimitiveData
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D] {I : Type w}
  {C : Family A D I} {E : Type z} [DGCategory A E] {F : DGFunctor A D E}
variable (P : PrimitiveData A D I C E F)

lemma boundaryAction_pathEvaluation (i : I) (w : List I) (y : D) :
    ((tensorLeftHom (C.generator A D I i) (C.term A D I w (C.target i) y)
      (homObject A E (F.obj (C.target i)) (F.obj y))).f 0
        (P.pathEvaluation w (C.target i) y)).comp
      (δ 0 1 (P.primitiveAction i (F.obj y))) (zero_add 1) =
    (C.replaceHead A D I i w y).comp (P.pathEvaluation w (C.source i) y) (add_zero 1) := by
  have h := tensorCochain_interchange (C.generator A D I i)
    (homObject A D (C.source i) (C.target i))
    (C.term A D I w (C.target i) y) (homObject A E (F.obj (C.target i)) (F.obj y))
    1 0 1 (add_zero 1) (zero_add 1)
    (C.boundaryCochain A D I i) (P.pathEvaluation w (C.target i) y)
  simp only [mul_zero, Int.negOnePow_zero, one_smul] at h
  have he :
      ((tensorLeftHom (homObject A D (C.source i) (C.target i))
        (C.term A D I w (C.target i) y)
        (homObject A E (F.obj (C.target i)) (F.obj y))).f 0
          (P.pathEvaluation w (C.target i) y)).comp
        (Cochain.ofHom (P.boundaryOriginalAction i (F.obj y))) (zero_add 0) =
      (tensorZeroCochain (Cochain.ofHom (F.map (C.source i) (C.target i)))
        (P.pathEvaluation w (C.target i) y)).comp
        (Cochain.ofHom (eComp (Complex A) (F.obj (C.source i)) (F.obj (C.target i)) (F.obj y)))
          (zero_add 0) := by
    rw [boundaryOriginalAction, Cochain.ofHom_comp,
      ← Cochain.comp_assoc_of_third_is_zero_cochain, ← tensorZeroCochain_ofHom_left]
  rw [primitiveAction_differential, ← Cochain.comp_assoc_of_third_is_zero_cochain, ← h,
    Cochain.comp_assoc_of_third_is_zero_cochain, he, ← pathEvaluation_prepend,
    ← Cochain.comp_assoc_of_second_is_zero_cochain]
  rfl

end SerrePositivity.DifferentialGraded.DGCellAttachment.Family.PrimitiveData
