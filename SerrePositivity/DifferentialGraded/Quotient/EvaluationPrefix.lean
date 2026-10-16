module
public import SerrePositivity.DifferentialGraded.Quotient.PathEvaluation
public import SerrePositivity.DifferentialGraded.Quotient.ContractionAction
public import SerrePositivity.DifferentialGraded.Complexes.TensorZeroCochainLeftMap

/-! # 固定前方Homとεによる評価作用・非空pathの微分入力 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] {D : Type v} [DGCategory A D]
  {S : Set D} {E : Type w} [DGCategory A E]

/-- 前方の元のHomをFで送り、既に評価された後方Homと合成するchain map。 -/
def evaluationOriginalAction (C : ContractedFunctor A D S E) (b : S) (x y : D) :
    homObject A D x b.val ⊗ homObject A E (C.toDGFunctor.obj b.val) (C.toDGFunctor.obj y) ⟶
      homObject A E (C.toDGFunctor.obj x) (C.toDGFunctor.obj y) :=
  (C.toDGFunctor.map x b.val ▷ homObject A E (C.toDGFunctor.obj b.val) (C.toDGFunctor.obj y)) ≫
    eComp (Complex A) (C.toDGFunctor.obj x) (C.toDGFunctor.obj b.val) (C.toDGFunctor.obj y)

/-- 前方Homと指定εを評価する固定の次数0 cochain。 -/
def evaluationPrefixAction (C : ContractedFunctor A D S E) (b : S) (x y : D) :
    Cochain (homObject A D x b.val ⊗
      (epsilonComplex A ⊗ homObject A E (C.toDGFunctor.obj b.val) (C.toDGFunctor.obj y)))
      (homObject A E (C.toDGFunctor.obj x) (C.toDGFunctor.obj y)) 0 :=
  ((tensorLeftHom (homObject A D x b.val)
    (epsilonComplex A ⊗ homObject A E (C.toDGFunctor.obj b.val) (C.toDGFunctor.obj y))
    (homObject A E (C.toDGFunctor.obj b.val) (C.toDGFunctor.obj y))).f 0
      (contractionAction A C b (C.toDGFunctor.obj y))).comp
    (Cochain.ofHom (evaluationOriginalAction A C b x y)) (zero_add 0)

lemma evaluationPrefixAction_differential (C : ContractedFunctor A D S E) (b : S) (x y : D) :
    δ 0 1 (evaluationPrefixAction A C b x y) =
    (eraseMiddle A (homObject A D x b.val)
      (homObject A E (C.toDGFunctor.obj b.val) (C.toDGFunctor.obj y))).comp
      (Cochain.ofHom (evaluationOriginalAction A C b x y)) (add_zero 1) := by
  rw [evaluationPrefixAction, δ_comp_ofHom,
    homComplexMap_differential (tensorLeftHom _ _ _) 0 1, contractionAction_differential,
    eraseMiddle_eq_tensorLeft]

lemma pathEvaluation_cons_action (C : ContractedFunctor A D S E) (b : S) (w : Word S) (x y : D) :
    pathEvaluation A C (b :: w) x y =
    ((tensorLeftHom (homObject A D x b.val)
      (epsilonComplex A ⊗ term A D w b.val y)
      (epsilonComplex A ⊗ homObject A E (C.toDGFunctor.obj b.val) (C.toDGFunctor.obj y))).f 0
      ((tensorLeftHom (epsilonComplex A) (term A D w b.val y)
        (homObject A E (C.toDGFunctor.obj b.val) (C.toDGFunctor.obj y))).f 0
          (pathEvaluation A C w b.val y))).comp
      (evaluationPrefixAction A C b x y) (zero_add 0) := by
  change (tensorZeroCochain (Cochain.ofHom (C.toDGFunctor.map x b.val))
      ((tensorZeroCochain (contractionCochain A C b) (pathEvaluation A C w b.val y)).comp
        (Cochain.ofHom (eComp (Complex A) (C.toDGFunctor.obj b.val)
          (C.toDGFunctor.obj b.val) (C.toDGFunctor.obj y))) (zero_add 0))).comp
      (Cochain.ofHom (eComp (Complex A) (C.toDGFunctor.obj x)
        (C.toDGFunctor.obj b.val) (C.toDGFunctor.obj y))) (zero_add 0) = _
  rw [contractionAction_evaluate, tensorZeroCochain_ofHom_left, tensorLeftHom_cochain_comp]
  simp only [Cochain.comp_assoc_of_third_is_zero_cochain, ← Cochain.ofHom_comp]
  rfl

lemma evaluationPrefixAction_evaluation_differential (C : ContractedFunctor A D S E)
    (b : S) (x y : D) (P : Complex A)
    (f : Cochain P (homObject A E (C.toDGFunctor.obj b.val) (C.toDGFunctor.obj y)) 0) :
    δ 0 1 (((tensorLeftHom (homObject A D x b.val) (epsilonComplex A ⊗ P)
      (epsilonComplex A ⊗ homObject A E (C.toDGFunctor.obj b.val) (C.toDGFunctor.obj y))).f 0
      ((tensorLeftHom (epsilonComplex A) P
        (homObject A E (C.toDGFunctor.obj b.val) (C.toDGFunctor.obj y))).f 0 f)).comp
      (evaluationPrefixAction A C b x y) (zero_add 0)) =
    (eraseMiddle A (homObject A D x b.val) P).comp
      ((tensorZeroCochain (Cochain.ofHom (C.toDGFunctor.map x b.val)) f).comp
        (Cochain.ofHom (eComp (Complex A) (C.toDGFunctor.obj x)
          (C.toDGFunctor.obj b.val) (C.toDGFunctor.obj y))) (zero_add 0)) (add_zero 1) +
    ((tensorLeftHom (homObject A D x b.val) (epsilonComplex A ⊗ P)
      (epsilonComplex A ⊗ homObject A E (C.toDGFunctor.obj b.val) (C.toDGFunctor.obj y))).f 1
      ((tensorLeftHom (epsilonComplex A) P
        (homObject A E (C.toDGFunctor.obj b.val) (C.toDGFunctor.obj y))).f 1 (δ 0 1 f))).comp
      (evaluationPrefixAction A C b x y) (add_zero 1) := by
  rw [δ_comp _ _ (zero_add 0) 1 1 1 (zero_add 1) (zero_add 1) (zero_add 1),
    evaluationPrefixAction_differential,
    homComplexMap_differential (tensorLeftHom _ _ _) 0 1,
    homComplexMap_differential (tensorLeftHom _ _ _) 0 1]
  simp only [Int.negOnePow_zero, one_smul]
  rw [← Cochain.comp_assoc_of_third_is_zero_cochain, eraseMiddle_cochain_zero,
    Cochain.comp_assoc_of_third_is_zero_cochain, tensorZeroCochain_ofHom_left,
    Cochain.comp_assoc_of_third_is_zero_cochain, ← Cochain.ofHom_comp]
  rfl

end SerrePositivity.DifferentialGraded.DGQuotient
