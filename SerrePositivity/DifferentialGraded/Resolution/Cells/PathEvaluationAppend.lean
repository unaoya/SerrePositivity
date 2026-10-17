module
public import SerrePositivity.DifferentialGraded.Resolution.Cells.PathEvaluationPrepend
public import SerrePositivity.DifferentialGraded.Complexes.TensorZeroCochainEvaluation

/-! # 指定原始元による評価は任意二pathの連結を保つ -/
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

lemma pathEvaluation_append (w v : List I) (x y z : D) :
    (Cochain.ofHom (C.appendMap A D I w v x y z)).comp
      (P.pathEvaluation (w ++ v) x z) (zero_add 0) =
    (tensorZeroCochain (P.pathEvaluation w x y) (P.pathEvaluation v y z)).comp
      (Cochain.ofHom (eComp (Complex A) (F.obj x)
        (F.obj y) (F.obj z))) (zero_add 0) := by
  induction w generalizing x with
  | nil => simpa only [Family.appendMap, List.nil_append, pathEvaluation_nil] using
      P.pathEvaluation_prepend v x y z
  | cons b w ih =>
    have hinner := tensorCarry_evaluation (P.cochain b)
      (P.pathEvaluation w (C.target b) y) (P.pathEvaluation v y z)
      (P.pathEvaluation (w ++ v) (C.target b) z)
      (C.appendMap A D I w v (C.target b) y z)
      (eComp (Complex A) (F.obj (C.target b)) (F.obj y) (F.obj z))
      (eComp (Complex A) (F.obj (C.source b)) (F.obj (C.target b)) (F.obj y))
      (eComp (Complex A) (F.obj (C.source b)) (F.obj (C.target b)) (F.obj z))
      (eComp (Complex A) (F.obj (C.source b)) (F.obj y) (F.obj z))
      (ih (C.target b))
      (e_assoc' (Complex A) (F.obj (C.source b)) (F.obj (C.target b))
        (F.obj y) (F.obj z)).symm
    have h := tensorCarry_evaluation (Cochain.ofHom (F.map x (C.source b)))
      ((tensorZeroCochain (P.cochain b) (P.pathEvaluation w (C.target b) y)).comp
        (Cochain.ofHom (eComp (Complex A) (F.obj (C.source b))
          (F.obj (C.target b)) (F.obj y))) (zero_add 0))
      (P.pathEvaluation v y z)
      ((tensorZeroCochain (P.cochain b) (P.pathEvaluation (w ++ v) (C.target b) z)).comp
        (Cochain.ofHom (eComp (Complex A) (F.obj (C.source b))
          (F.obj (C.target b)) (F.obj z))) (zero_add 0))
      ((α_ (C.generator A D I b) (C.term A D I w (C.target b) y) (C.term A D I v y z)).hom ≫
        (C.generator A D I b) ◁ C.appendMap A D I w v (C.target b) y z)
      (eComp (Complex A) (F.obj (C.source b)) (F.obj y) (F.obj z))
      (eComp (Complex A) (F.obj x) (F.obj (C.source b)) (F.obj y))
      (eComp (Complex A) (F.obj x) (F.obj (C.source b)) (F.obj z))
      (eComp (Complex A) (F.obj x) (F.obj y) (F.obj z))
      hinner
      (e_assoc' (Complex A) (F.obj x) (F.obj (C.source b))
        (F.obj y) (F.obj z)).symm
    simpa only [pathEvaluation, appendMap, List.cons_append] using h

end SerrePositivity.DifferentialGraded.DGCellAttachment.Family.PrimitiveData
