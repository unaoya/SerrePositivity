module
public import SerrePositivity.DifferentialGraded.Quotient.PathEvaluation
public import SerrePositivity.DifferentialGraded.Quotient.PathComposition
public import SerrePositivity.DifferentialGraded.Complexes.TensorJoinEvaluation

/-! # 元のHomを先頭合成する操作と有限path評価の整合性 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] {D : Type v} [DGCategory A D]
  {S : Set D} {E : Type w} [DGCategory A E]

lemma pathEvaluation_prepend (C : ContractedFunctor A D S E) (w : Word S) (x y z : D) :
    (Cochain.ofHom (prependMap A D w x y z)).comp (pathEvaluation A C w x z) (zero_add 0) =
    (tensorZeroCochain (Cochain.ofHom (C.toDGFunctor.map x y)) (pathEvaluation A C w y z)).comp
      (Cochain.ofHom (eComp (Complex A) (C.toDGFunctor.obj x)
        (C.toDGFunctor.obj y) (C.toDGFunctor.obj z))) (zero_add 0) := by
  cases w with
  | nil =>
    simpa only [pathEvaluation_nil, prependMap_nil, tensorZeroCochain_ofHom,
      ← Cochain.ofHom_comp] using
      congrArg (fun f => Cochain.ofHom f) (C.toDGFunctor.map_comp x y z)
  | cons b w =>
    have h := tensorJoin_evaluation
      (homObject A D x y) (homObject A D y b.val) (homObject A D x b.val)
      (homObject A E (C.toDGFunctor.obj x) (C.toDGFunctor.obj y))
      (homObject A E (C.toDGFunctor.obj y) (C.toDGFunctor.obj b.val))
      (homObject A E (C.toDGFunctor.obj x) (C.toDGFunctor.obj b.val))
      (epsilonComplex A ⊗ term A D w b.val z)
      (homObject A E (C.toDGFunctor.obj b.val) (C.toDGFunctor.obj z))
      (homObject A E (C.toDGFunctor.obj y) (C.toDGFunctor.obj z))
      (homObject A E (C.toDGFunctor.obj x) (C.toDGFunctor.obj z))
      (C.toDGFunctor.map x y) (C.toDGFunctor.map y b.val) (C.toDGFunctor.map x b.val)
      (eComp (Complex A) x y b.val)
      (eComp (Complex A) (C.toDGFunctor.obj x) (C.toDGFunctor.obj y) (C.toDGFunctor.obj b.val))
      (eComp (Complex A) (C.toDGFunctor.obj x) (C.toDGFunctor.obj b.val) (C.toDGFunctor.obj z))
      (eComp (Complex A) (C.toDGFunctor.obj y) (C.toDGFunctor.obj b.val) (C.toDGFunctor.obj z))
      (eComp (Complex A) (C.toDGFunctor.obj x) (C.toDGFunctor.obj y) (C.toDGFunctor.obj z))
      (C.toDGFunctor.map_comp x y b.val)
      (e_assoc' (Complex A) (C.toDGFunctor.obj x) (C.toDGFunctor.obj y)
        (C.toDGFunctor.obj b.val) (C.toDGFunctor.obj z)).symm
      ((tensorZeroCochain (contractionCochain A C b) (pathEvaluation A C w b.val z)).comp
        (Cochain.ofHom (eComp (Complex A) (C.toDGFunctor.obj b.val)
          (C.toDGFunctor.obj b.val) (C.toDGFunctor.obj z))) (zero_add 0))
    simpa only [pathEvaluation, prependMap, tensorHom_id] using h

end SerrePositivity.DifferentialGraded.DGQuotient
