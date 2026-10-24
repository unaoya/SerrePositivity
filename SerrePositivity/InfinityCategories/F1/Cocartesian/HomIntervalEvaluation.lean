module

public import SerrePositivity.InfinityCategories.F1.FunctorCategories.FunctorEvaluationLifting
public import SerrePositivity.InfinityCategories.F1.Coherent.HomIntervalNaturality
public import SerrePositivity.InfinityCategories.F1.Cocartesian.TransportDiagramHomInterval

/-!
概要：元の分類先の区間 Hom の成分評価を、元の strict Hom の成分と厳密に結ぶ。
方針：実際の実現の評価公式を、標準の coherent Hom 比較の自然性へ接続する。
規約：独立な同値を元の Hom 作用の代わりに使わない。
使われ方：一次元セル上で、同じ Hom 作用を二つの成分と比較する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 分類先の実際の区間 Hom を底の同じ対象で評価し、端点を元の値に正規化する。 -/
def cocartesianHomIntervalEvaluation {C : Type u} [Category.{u} C]
    (F G : CocartesianTransportDiagramCategory C) (c : C) :
    intervalMappingSpace
      (functorVertex (qCatDiagramCoherentNerve (cocartesianTransportDiagramValueFunctor F)))
      (functorVertex (qCatDiagramCoherentNerve (cocartesianTransportDiagramValueFunctor G))) ⟶
    intervalMappingSpace (coherentNerveVertex (cocartesianTransportDiagramValue F c))
      (coherentNerveVertex (cocartesianTransportDiagramValue G c)) :=
  intervalMappingPostOfEq (evaluateFunctorAt
    (X := (SSet.uliftFunctor.{u + 1, u}).obj (nerve C)) (ULift.up (nerveVertex c))) _ _
    (by rw [evaluateFunctorAt_functorVertex];
        exact qCatDiagramCoherentNerve_vertex (cocartesianTransportDiagramValueFunctor F) c)
    (by rw [evaluateFunctorAt_functorVertex];
        exact qCatDiagramCoherentNerve_vertex (cocartesianTransportDiagramValueFunctor G) c)

/-- 元の全 Hom の作用と実際の成分評価は、同じ成分写像と標準の Hom 比較で可換。 -/
lemma cocartesianTransportDiagramHomInterval_evaluation
    {C : Type u} [Category.{u} C] (F G : CocartesianTransportDiagramCategory C) (c : C) :
    cocartesianTransportDiagramHomInterval F G ≫ cocartesianHomIntervalEvaluation F G c =
      (SSet.uliftFunctor.{u + 1, u}).map
        ((cocartesianTransportDiagramEvaluationEnriched c).map F G) ≫
      coherentHomIntervalComparison
        (cocartesianTransportDiagramValue F c) (cocartesianTransportDiagramValue G c) := by
  apply intervalMappingUncurry_injective
  rw [cocartesianHomIntervalEvaluation, intervalMappingPostOfEq_uncurry,
    cocartesianTransportDiagramHomInterval_evaluate]
  have h := congrArg (fun f => intervalMappingUncurry f)
    (coherentHomIntervalComparison_enriched_naturality
      (cocartesianTransportDiagramEvaluationEnriched c) F G)
  rw [intervalMappingPostOfEq_uncurry] at h
  unfold coherentHomIntervalComparison at h
  rw [pinchedHomToIntervalMappingSpace_uncurry] at h
  exact h

/-- 元の分類先の成分評価は、単射な同値を右に持ち上げる。 -/
lemma kanEquivalenceLifting_cocartesianHomIntervalEvaluation
    {C : Type u} [Category.{u} C] (F G : CocartesianTransportDiagramCategory C) (c : C) :
    SerrePositivity.InfinityCategories.F1B.EquivalenceLifting (cocartesianHomIntervalEvaluation F G c) :=
  kanEquivalenceLifting_intervalMappingPostOfEq _
    (kanEquivalenceLifting_evaluateFunctorAt _) _ _ _ _

open HomotopicalAlgebra SSet.modelCategoryQuillen in
/-- 元の分類先の同じ区間 Hom の成分評価は Kan fibration。 -/
lemma cocartesianHomIntervalEvaluation_fibration
    {C : Type u} [Category.{u} C] (F G : CocartesianTransportDiagramCategory C) (c : C) :
    Fibration (cocartesianHomIntervalEvaluation F G c) :=
  intervalMappingPostOfEq_evaluateFunctorAt_fibration _ _ _ _ _

end SerrePositivity.InfinityCategories
