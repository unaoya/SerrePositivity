module
public import SerrePositivity.KST.Fibration.ContractibleRestrictionComparison
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.FunctorPrismEdgeLifting
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.FunctorPrismTriangles

/-! # 指定部分上で恒等の元の比較辺を、同じ固定部分を持つ全円柱へ評価する -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration
variable {A B Z : SSet.{u}} [Quasicategory Z] {i : A ⟶ B} {f g : B ⟶ Z}
  (E : FixedRestrictionFunctorEdge i f g)

/-- 元の全比較辺を、元の関手族を両端に持つ同じ全円柱として評価する。 -/
def FixedRestrictionFunctorEdge.prism : (Δ[1] : SSet.{u}) ⊗ B ⟶ Z := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.functorEdgePrism E.edge

/-- 同じ円柱の始点は、元の第一関手族そのもの。 -/
theorem FixedRestrictionFunctorEdge.prism_zero :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 B ≫ E.prism = f := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.functorEdgePrism_zero E.edge

/-- 同じ円柱の終点は、元の第二関手族そのもの。 -/
theorem FixedRestrictionFunctorEdge.prism_one :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 B ≫ E.prism = g := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.functorEdgePrism_one E.edge

/-- 指定部分上の全時刻の円柱は、元の同じ制限関手を時間に関して定値にした射。 -/
theorem FixedRestrictionFunctorEdge.prism_restriction :
    (Δ[1] ◁ i) ≫ E.prism = snd (Δ[1] : SSet.{u}) A ≫ i ≫ f := by
  rw [FixedRestrictionFunctorEdge.prism, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.functorEdgePrism, ← _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.functorFamilyPrism_pre,
    SSet.yonedaEquiv_symm_comp, E.restriction]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.functorEdgePrism_id (i ≫ f)

end SerrePositivity.KST.Fibration
