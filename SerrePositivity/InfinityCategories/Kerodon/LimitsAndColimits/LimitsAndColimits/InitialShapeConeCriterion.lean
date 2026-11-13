module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.EquivalencePath
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.InvertibleEdgeLifting
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.JoinCells
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoreLimit
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.LimitConeExtension
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.FunctorVertexCone
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.FunctorVertexConeReindex
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.PointConeIdentityComparison
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.SimplexConeRestriction

/-!
概要：始点への left anodyne な制限を持つ形状の極限錐を元の脚で判定する。
方針：元の錐を一点に制限し、標準辺への厳密な読み替えと可逆性判定を合成する。
規約：指定された全錐を保持。使われ方：単体形状の coherent filtered 極限交換。

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

/-- 元の錐の頂点から指定された形状の一点への標準脚。 -/
def coneInitialLeg {K : SSet.{u}} (a : (Δ[0] : SSet.{u}) ⟶ K) :
    (Δ[1] : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u}) K :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).inv ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 Δ[0]) a

/-- 始点への left anodyne 制限がある形状では、指定脚の可逆性が元の極限性を判定。 -/
lemma isLimitCone_functorVertexCone_iff_initialLeg {K X : SSet.{u}} [Quasicategory X]
    (a : (Δ[0] : SSet.{u}) ⟶ K) [Mono a] (ha : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftAnodyneExtensions a)
    (v : ((ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u}) K)).obj X) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.functorVertexCone v) ↔
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsEquivalencePathVertex (((pre (coneInitialLeg a)).app X).app (Opposite.op ⦋0⦌) v) := by
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalFunctorVertexEdge
      (((pre (coneInitialLeg a)).app X).app (Opposite.op ⦋0⦌) v) =
      SSet.yonedaEquiv ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).inv ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.restrictJoinCone (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.functorVertexCone v) a).val) := by
    unfold _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalFunctorVertexEdge
    rw [_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.functorVertexMap_precomp]
    rfl
  exact (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.isLimitCone_restrict_iff_of_leftAnodyne (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.functorVertexCone v) a ha).symm.trans
    ((_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.isLimitCone_point_iff_edge _).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr he.symm))

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
