module
public import SerrePositivity.DifferentialGraded.Quotient.Path.Evaluation
public import Mathlib.Data.ZMod.Basic

/-! # 評価の微分・最終Homのchain map・指定収縮保存の受入監査 -/
@[expose] public section
noncomputable section
universe u v w
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
open SerrePositivity.DifferentialGraded
open SerrePositivity.DifferentialGraded.DGQuotient
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E]

example (S : Set D) (C : ContractedFunctor A D S E) (x y : D) :
    δ 0 1 (internalEvaluation A C x y) =
      (erasure A D S x y).comp (internalEvaluation A C x y) (add_zero 1) :=
  internalEvaluation_differential A C x y

example (S : Set D) (C : ContractedFunctor A D S E) (x y : D) :
    quotientHom A D S x y ⟶ homObject A E (C.toDGFunctor.obj x) (C.toDGFunctor.obj y) :=
  quotientEvaluation A C x y

example (b : (Set.univ : Set PUnit.{1})) :
    (quotientEvaluation (ZMod 2) (canonicalContractedFunctor (ZMod 2) PUnit.{1} Set.univ)
      b.val b.val).f (-1) (epsilonElement (ZMod 2) PUnit.{1} Set.univ b) =
    (canonicalContractedFunctor (ZMod 2) PUnit.{1} Set.univ).homotopy b :=
  quotientEvaluation_epsilon (ZMod 2) (canonicalContractedFunctor (ZMod 2) PUnit.{1} Set.univ) b

#print axioms SerrePositivity.DifferentialGraded.tensorZeroCochain_ofHom_left
#print axioms SerrePositivity.DifferentialGraded.perturbSourceMap
#print axioms SerrePositivity.DifferentialGraded.perturbSourceMap_f
#print axioms SerrePositivity.DifferentialGraded.DGQuotient.eraseHead_cochain_zero
#print axioms SerrePositivity.DifferentialGraded.DGQuotient.eraseMiddle_cochain_zero
#print axioms SerrePositivity.DifferentialGraded.DGQuotient.contractionAction
#print axioms SerrePositivity.DifferentialGraded.DGQuotient.contractionAction_differential
#print axioms SerrePositivity.DifferentialGraded.DGQuotient.contractionAction_evaluate
#print axioms SerrePositivity.DifferentialGraded.DGQuotient.contractionAction_evaluation_differential
#print axioms SerrePositivity.DifferentialGraded.DGQuotient.evaluationOriginalAction
#print axioms SerrePositivity.DifferentialGraded.DGQuotient.evaluationPrefixAction
#print axioms SerrePositivity.DifferentialGraded.DGQuotient.evaluationPrefixAction_differential
#print axioms SerrePositivity.DifferentialGraded.DGQuotient.pathEvaluation_cons_action
#print axioms SerrePositivity.DifferentialGraded.DGQuotient.evaluationPrefixAction_evaluation_differential
#print axioms SerrePositivity.DifferentialGraded.DGQuotient.pathEvaluationTail
#print axioms SerrePositivity.DifferentialGraded.DGQuotient.pathEvaluation_cons_differential
#print axioms SerrePositivity.DifferentialGraded.DGQuotient.internalEvaluation_prefixPath
#print axioms SerrePositivity.DifferentialGraded.DGQuotient.pathEvaluationTail_internalEvaluation
#print axioms SerrePositivity.DifferentialGraded.DGQuotient.pathEvaluation_differential
#print axioms SerrePositivity.DifferentialGraded.DGQuotient.internalEvaluation_differential
#print axioms SerrePositivity.DifferentialGraded.DGQuotient.quotientEvaluation
#print axioms SerrePositivity.DifferentialGraded.DGQuotient.quotientEvaluation_f
#print axioms SerrePositivity.DifferentialGraded.DGQuotient.quotientEvaluation_original
#print axioms SerrePositivity.DifferentialGraded.DGQuotient.quotientEvaluation_epsilon
#print axioms SerrePositivity.DifferentialGraded.DGQuotient.quotientEvaluation_path
#print axioms SerrePositivity.DifferentialGraded.DGQuotient.quotientEvaluation_unit
