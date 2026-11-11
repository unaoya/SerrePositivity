module
public import SerrePositivity.KST.Fibration.ComposableWeakArrowSPullback
public import SerrePositivity.KST.SConstruction.FunctorVertexEvaluation

/-! # 元の W 辺の端点と一点図式の完全な同型

共有端点の一点図式を元の安定圏に戻し、相対 cofiber の subobject 評価と照合する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
open SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.Fibration

/-- 一点上の全図式を元の安定圏へ戻す、厳密な完全同型。 -/
def ambientPointExactIso (B : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}) :
    ambientDiagramModel (Δ[0] : SSet.{u}) B ≅ sInputModel B where
  hom := ⟨(SConstruction.pointFunctorEvaluationIso B.obj).hom,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor.preservesZero, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor.preservesCofiber⟩
  inv := ⟨(SConstruction.pointFunctorEvaluationIso B.obj).inv,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor.preservesZero, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor.preservesCofiber⟩
  hom_inv_id := Subtype.ext (SConstruction.pointFunctorEvaluationIso B.obj).hom_inv_id
  inv_hom_id := Subtype.ext (SConstruction.pointFunctorEvaluationIso B.obj).inv_hom_id

/-- W 辺の元の始点を取る完全関手。 -/
def weakArrowSourceExact {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) :
    weakArrowModel q ⟶ sInputModel B :=
  weakArrowSourceDiagram q ≫ (ambientPointExactIso B).hom

/-- W 辺の元の終点を取る完全関手。 -/
def weakArrowTargetExact {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) :
    weakArrowModel q ⟶ sInputModel B :=
  weakArrowTargetDiagram q ≫ (ambientPointExactIso B).hom

/-- 始点射は元の全矢図式の始点評価そのもの。 -/
lemma weakArrowSourceExact_val {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) :
    (weakArrowSourceExact q).val = (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ (weakArrowPredicate q)).ι ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) := by
  change ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ (weakArrowPredicate q)).ι ≫
    (MonoidalClosed.pre (stdSimplex.δ (1 : Fin 2))).app B.obj) ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 1)) = _
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.stable_pre_evaluateFunctorAt]
  rfl

/-- 終点射も元の全矢図式の終点評価そのもの。 -/
lemma weakArrowTargetExact_val {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) :
    (weakArrowTargetExact q).val = (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ (weakArrowPredicate q)).ι ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) := by
  change ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ (weakArrowPredicate q)).ι ≫
    (MonoidalClosed.pre (stdSimplex.δ (0 : Fin 2))).app B.obj) ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 1)) = _
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.stable_pre_evaluateFunctorAt]
  rfl

/-- 全相対 cofiber 補完から元の W 辺の始点を取ると、同じ subobject 評価を回収する。 -/
lemma weakCofiberProjection_source {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) :
    (weakArrowCofiberEquivalence q).hom ≫ weakArrowSourceExact q =
      relativeCofiberSubobject (ClosedStablePredicate.top (sInputModel B))
        (kernelClosedPredicate q) ≫ closedStableInclusion (ClosedStablePredicate.top
          (sInputModel B)) := by
  rw [relativeCofiberSubobject_inclusion]
  apply Subtype.ext
  change weakCofiberProjection q ≫ (weakArrowSourceExact q).val = _
  rw [weakArrowSourceExact_val, ← Category.assoc, weakCofiberProjection_ι, Category.assoc]
  congr 1

end SerrePositivity.KST.Fibration
