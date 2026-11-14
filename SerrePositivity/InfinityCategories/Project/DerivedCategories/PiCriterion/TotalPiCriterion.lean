module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion.TotalComparison
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion.KanMapCriterion
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.SpaceEdgeValueEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanInvertible

/-!
概要：元の coherent 余錐の余極限性を、全空間比較の全基点 π で判定する。
方針：余錐全体から選んだ頂点比較辺を同じ Kan 射へ読み戻し、Whitehead を適用。
規約：filtered な各段での元ごとの条件への変換は別途必要。
使われ方：有限段階検出から native な余極限性へ戻す最後の判定。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion

/-- 指定空間辺の可逆性を、その同じ Kan 射の全基点 π で判定する。 -/
lemma spaceEdge_invertible_iff_piCriterion {x y : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} _⦋0⦌}
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}.Edge x y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge e ↔ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion.KanMapPiCriterion (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.spaceInfinityEdgeValue e) := by
  constructor
  · intro he
    exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion.homotopyEquivalence_iff_kanMapPiCriterion _).mp
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.spaceInfinityEdgeValue_isQCatEquivalence e he).isSimplicialHomotopyEquivalence
  · intro h
    have he := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentKanEdge_isInvertible_of_isQCatEquivalence
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion.homotopyEquivalence_iff_kanMapPiCriterion _).mpr h).isQCatEquivalence
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.spaceInfinityEdgeValue_edge e)).mp he

variable {B : SSet.{u}}

/-- 元の余錐比較の頂点射を表す、端点を固定した実際の辺。 -/
def totalVertexComparisonEdge
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone F) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}.Edge (_root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalCocone F).vertex c.vertex :=
  SSet.Edge.ofTruncated (Classical.choose (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.homotopyCategory_homMk_surjective
    (_root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalCocone F).vertex c.vertex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion.totalVertexComparison F c)))

/-- 選んだ辺は元の余錐全体からの比較射を表す。 -/
lemma totalVertexComparisonEdge_homMk
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone F) :
    SSet.Truncated.HomotopyCategory.homMk (totalVertexComparisonEdge F c).toTruncated =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion.totalVertexComparison F c :=
  Classical.choose_spec (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.homotopyCategory_homMk_surjective
    (_root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalCocone F).vertex c.vertex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion.totalVertexComparison F c))

/-- 全空間から候補頂点への同じ比較を Kan 射として読む。 -/
def totalValueComparison
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone F) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.spaceInfinityObject (_root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalCocone F).vertex ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.spaceInfinityObject c.vertex :=
  _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.spaceInfinityEdgeValue (totalVertexComparisonEdge F c)

/-- 元の余錐は余極限であることと、全空間比較の π₀・全基点正次数の全単射は同値。 -/
lemma isColimitCone_iff_totalPiCriterion
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone F) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c ↔ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion.KanMapPiCriterion (totalValueComparison F c) := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion.isColimitCone_iff_totalVertexComparison_isIso]
  have h : IsIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion.totalVertexComparison F c) ↔
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (totalVertexComparisonEdge F c) := by
    change IsIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion.totalVertexComparison F c) ↔
      IsIso (SSet.Truncated.HomotopyCategory.homMk
        (totalVertexComparisonEdge F c).toTruncated)
    rw [totalVertexComparisonEdge_homMk]
  exact h.trans (spaceEdge_invertible_iff_piCriterion (totalVertexComparisonEdge F c))

end SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion
