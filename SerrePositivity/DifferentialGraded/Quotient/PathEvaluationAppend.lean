module
public import SerrePositivity.DifferentialGraded.Quotient.PathEvaluationPrepend
public import SerrePositivity.DifferentialGraded.Complexes.TensorZeroCochainEvaluation

/-! # 指定収縮による評価は任意二pathの連結を保つ -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] {D : Type v} [DGCategory A D]
  {S : Set D} {E : Type w} [DGCategory A E]

lemma pathEvaluation_append (C : ContractedFunctor A D S E) (w v : Word S) (x y z : D) :
    (Cochain.ofHom (appendMap A D w v x y z)).comp
      (pathEvaluation A C (w ++ v) x z) (zero_add 0) =
    (tensorZeroCochain (pathEvaluation A C w x y) (pathEvaluation A C v y z)).comp
      (Cochain.ofHom (eComp (Complex A) (C.toDGFunctor.obj x)
        (C.toDGFunctor.obj y) (C.toDGFunctor.obj z))) (zero_add 0) := by
  induction w generalizing x with
  | nil => simpa only [appendMap_nil_left, List.nil_append, pathEvaluation_nil] using
      pathEvaluation_prepend A C v x y z
  | cons b w ih =>
    have hinner := tensorCarry_evaluation (contractionCochain A C b)
      (pathEvaluation A C w b.val y) (pathEvaluation A C v y z)
      (pathEvaluation A C (w ++ v) b.val z)
      (appendMap A D w v b.val y z)
      (eComp (Complex A) (C.toDGFunctor.obj b.val) (C.toDGFunctor.obj y) (C.toDGFunctor.obj z))
      (eComp (Complex A) (C.toDGFunctor.obj b.val) (C.toDGFunctor.obj b.val) (C.toDGFunctor.obj y))
      (eComp (Complex A) (C.toDGFunctor.obj b.val) (C.toDGFunctor.obj b.val) (C.toDGFunctor.obj z))
      (eComp (Complex A) (C.toDGFunctor.obj b.val) (C.toDGFunctor.obj y) (C.toDGFunctor.obj z))
      (ih b.val)
      (e_assoc' (Complex A) (C.toDGFunctor.obj b.val) (C.toDGFunctor.obj b.val)
        (C.toDGFunctor.obj y) (C.toDGFunctor.obj z)).symm
    have h := tensorCarry_evaluation (Cochain.ofHom (C.toDGFunctor.map x b.val))
      ((tensorZeroCochain (contractionCochain A C b) (pathEvaluation A C w b.val y)).comp
        (Cochain.ofHom (eComp (Complex A) (C.toDGFunctor.obj b.val)
          (C.toDGFunctor.obj b.val) (C.toDGFunctor.obj y))) (zero_add 0))
      (pathEvaluation A C v y z)
      ((tensorZeroCochain (contractionCochain A C b) (pathEvaluation A C (w ++ v) b.val z)).comp
        (Cochain.ofHom (eComp (Complex A) (C.toDGFunctor.obj b.val)
          (C.toDGFunctor.obj b.val) (C.toDGFunctor.obj z))) (zero_add 0))
      ((α_ (epsilonComplex A) (term A D w b.val y) (term A D v y z)).hom ≫
        (epsilonComplex A) ◁ appendMap A D w v b.val y z)
      (eComp (Complex A) (C.toDGFunctor.obj b.val) (C.toDGFunctor.obj y) (C.toDGFunctor.obj z))
      (eComp (Complex A) (C.toDGFunctor.obj x) (C.toDGFunctor.obj b.val) (C.toDGFunctor.obj y))
      (eComp (Complex A) (C.toDGFunctor.obj x) (C.toDGFunctor.obj b.val) (C.toDGFunctor.obj z))
      (eComp (Complex A) (C.toDGFunctor.obj x) (C.toDGFunctor.obj y) (C.toDGFunctor.obj z))
      hinner
      (e_assoc' (Complex A) (C.toDGFunctor.obj x) (C.toDGFunctor.obj b.val)
        (C.toDGFunctor.obj y) (C.toDGFunctor.obj z)).symm
    simpa only [pathEvaluation, appendMap, List.cons_append] using h

end SerrePositivity.DifferentialGraded.DGQuotient
