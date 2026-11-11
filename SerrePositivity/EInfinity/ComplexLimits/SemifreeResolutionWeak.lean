module

public import SerrePositivity.EInfinity.ComplexLimits.SemifreeRingEvaluation
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleResolvedInvertsQuasiIso
public import SerrePositivity.DifferentialGraded.Derived.Basic

/-!
# 既存 D(R) への実分解は元の複体の準同型辺を反転する

概要：元の複体の辺を同じ一点 dg 加群の出力分解へ送り、可逆性を得る。
方針：全 Hom の評価が元の複体 dg 関手を厳密に回収することを使う。
規約：元の対象の cofibrancy や semifree 性を要求しない。
使われ方：CAlg_R の普遍性による実忘却 ∞ 関手の延長。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.ComplexLimits
open SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded SSet

open scoped Simplicial
variable (A : Type u) [CommRing A]

lemma complexSemifreeResolutionInfinity_invertsQuasiIso
    {x y : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (Complex A)) _⦋0⦌}
    (e : Truncated.Edge (X := (truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (Complex A))) x y)
    (he : QuasiIso ((closedToComplex A).map (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.edgeClosed e))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (X := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityCategory A)
      (e.map ((truncation 2).map (complexSemifreeResolutionInfinity A))) := by
  have hm : moduleQuasiIso A PUnit.{1} ((ringConstantDG A).onClosed.map (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.edgeClosed e)) := by
    apply (ringModuleQuasiIso_iff A _).mpr
    change QuasiIso ((closedToComplex A).map
      (((ringConstantDG A).comp (moduleEvaluationDG A PUnit.{1} PUnit.unit)).onClosed.map
        (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.edgeClosed e)))
    rw [ringConstantDG_comp_evaluation]
    exact he
  have h := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity_invertsQuasiIso A (Complex A) PUnit.{1}
    (ringConstantDG A) e hm
  exact h.map (semifreeRingEvaluationInfinity A)

end SerrePositivity.EInfinity.ComplexLimits
