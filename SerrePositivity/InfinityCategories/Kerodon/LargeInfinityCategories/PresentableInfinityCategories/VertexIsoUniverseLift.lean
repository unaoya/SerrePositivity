module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.QCatEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ConstantFunctor
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.SSetProductEvaluation

/-!
概要：元の頂点同型を指定宇宙へ持ち上げる。
方針：一点上の定値関手同型を持ち上げ、同じ一点で評価する。
規約：同じ両端頂点の持ち上げを保持する。
使われ方：前層の実現頂点同型を大きい全 Hom 係数族へ送る。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 概要：元の頂点同型は指定された持ち上げ頂点間の同型を与える。
方針：一点上の同じ定値関手として持ち上げた後に評価する。
規約：追加の同型な対象を選ばない。
使われ方：全 Hom 族の宇宙を合わせた頂点比較。 -/
def liftVertexIso {X : SSet.{u}} [Quasicategory X] {x y : X _⦋0⦌}
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso x y) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (X := (SSet.uliftFunctor.{v, u}).obj X)
      (ULift.up x) (ULift.up y) := by
  have e' := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map e (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorMap (Δ[0] : SSet.{u}) X)
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorMap_vertex, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorMap_vertex] at e'
  let e'' : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (SSet.const x : (Δ[0] : SSet.{u}) ⟶ X) (SSet.const y) := e'
  have h := (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.FunctorIso.ulift.{u, v} e'').app
    (ULift.up (SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u}))))
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (X := (SSet.uliftFunctor.{v, u}).obj X)
    (ULift.up ((SSet.const x : (Δ[0] : SSet.{u}) ⟶ X).app _
    (SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u})))))
    (ULift.up ((SSet.const y : (Δ[0] : SSet.{u}) ⟶ X).app _
      (SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u}))))) at h
  simpa only [_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.ssetConst_zero_apply] using h

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
