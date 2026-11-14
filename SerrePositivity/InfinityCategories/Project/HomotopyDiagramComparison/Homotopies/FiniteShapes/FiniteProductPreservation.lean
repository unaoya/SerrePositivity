module

public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.MappingSpaces.UniverseLimits
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.SquareFunctorTransport

/-!
概要：小さい始域から大きい宇宙への ∞ 関手の有限積保存。
方針：元の有限離散図式の全極限錐を持ち上げ、同じ全錐の像の極限性を要求する。
規約：指定頂点と全ての脚を保つ。始域の有限積の存在は条件に含めない。
使われ方：HTT 5.5.8.8 の P_Σ と、反変前層の有限余積から積への保存。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison

/-- 小さい始域の元の有限離散極限錐を、その持ち上げの全錐ごと保存する条件。 -/
def PreservesFiniteProductsFromSmallSource {C : SSet.{u}} {X : SSet.{u + 1}}
    (F : (SSet.uliftFunctor.{u + 1, u}).obj C ⟶ X) : Prop :=
  ∀ (J : Type u) [Finite J] (p : nerve (Discrete J) ⟶ C) (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p),
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone c → _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCone F (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.JoinCone.ulift.{u, u + 1} c))

/-- 元の指定された有限積錐の像は、元の頂点と全ての脚を持つ極限錐。 -/
lemma PreservesFiniteProductsFromSmallSource.map_isLimit
    {C : SSet.{u}} {X : SSet.{u + 1}}
    {F : (SSet.uliftFunctor.{u + 1, u}).obj C ⟶ X}
    (hF : PreservesFiniteProductsFromSmallSource F)
    {J : Type u} [Finite J] {p : nerve (Discrete J) ⟶ C}
    {c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p} (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone c) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCone F (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.JoinCone.ulift.{u, u + 1} c)) := hF J p c hc

/-- 有限積保存は関手の同型で不変。底図式も像の全錐も元のものを使う。 -/
lemma preservesFiniteProductsFromSmallSource_iff_of_functorIso
    {C : SSet.{u}} {X : SSet.{u + 1}} [Quasicategory X]
    {F G : (SSet.uliftFunctor.{u + 1, u}).obj C ⟶ X} (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso F G) :
    PreservesFiniteProductsFromSmallSource F ↔ PreservesFiniteProductsFromSmallSource G := by
  constructor
  · intro h J _ p c hc
    exact (h J p c hc).of_functorIso (e.precomp (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.JoinCone.ulift.{u, u + 1} c).val)
  · intro h J _ p c hc
    exact (h J p c hc).of_functorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp e.symm (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.JoinCone.ulift.{u, u + 1} c).val)

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
