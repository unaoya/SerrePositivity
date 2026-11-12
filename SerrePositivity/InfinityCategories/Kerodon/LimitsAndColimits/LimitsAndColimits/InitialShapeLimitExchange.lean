module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.Cocone
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.EquivalencePath
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.JoinCells
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoreLimit
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.ArrowColimitInvertibility
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FunctorCoconeEvaluation
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FunctorCoconeReindex
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FunctorVertexCone
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InitialShapeConeCriterion

/-!
概要：始点で極限を検出できる形状では元の点ごとの余極限も極限錐を保つ。
方針：始点への元の脚の族を再添字付けし、指定余極限矢印の可逆性を使う。
規約：添字の filtered 性は不要。使われ方：有限セル帰納の単体条件。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

/-- 始点で検出できる形状の極限は、元の点ごとの余極限余錐で保存される。 -/
lemma pointwiseColimit_preserves_initialShapeLimits {J K X : SSet.{u}} [Quasicategory X]
    (a : (Δ[0] : SSet.{u}) ⟶ K) [Mono a] (ha : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftAnodyneExtensions a)
    {p : J ⟶ (ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u}) K)).obj X} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p)
    (hc : _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.IsPointwiseColimitCone c)
    (hp : ∀ j : J _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.functorVertexCone (p.app (Opposite.op ⦋0⦌) j))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.functorVertexCone c.vertex) := by
  let d := _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.reindexFunctorCocone c (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coneInitialLeg a)
  have hd : _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.IsPointwiseColimitCone d := hc.reindex _
  have hi : ∀ j : J _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsEquivalencePathVertex
      ((p ≫ (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coneInitialLeg a)).app X).app (Opposite.op ⦋0⦌) j) := by
    intro j
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isLimitCone_functorVertexCone_iff_initialLeg a ha
      (p.app (Opposite.op ⦋0⦌) j)).mp (hp j)
  have hv := _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.isEquivalencePathVertex_of_pointwiseColimit d hd hi
  rw [_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.reindexFunctorCocone_vertex] at hv
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isLimitCone_functorVertexCone_iff_initialLeg a ha c.vertex).mpr hv

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
