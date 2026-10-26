module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.PiCriterion.TotalComparison
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.PiCriterion.KanMapCriterion
public import SerrePositivity.InfinityCategories.F2.Compact.SpaceEdgeValueEquivalence
public import SerrePositivity.InfinityCategories.F1.Coherent.KanInvertible

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
namespace SerrePositivity.InfinityCategories.F2.PiCriterion

/-- 指定空間辺の可逆性を、その同じ Kan 射の全基点 π で判定する。 -/
lemma spaceEdge_invertible_iff_piCriterion {x y : SpaceInfinity.{u} _⦋0⦌}
    (e : SpaceInfinity.{u}.Edge x y) :
    IsInvertibleEdge e ↔ KanMapPiCriterion (spaceInfinityEdgeValue e) := by
  constructor
  · intro he
    exact (homotopyEquivalence_iff_kanMapPiCriterion _).mp
      (Compact.spaceInfinityEdgeValue_isQCatEquivalence e he).isSimplicialHomotopyEquivalence
  · intro h
    have he := coherentKanEdge_isInvertible_of_isQCatEquivalence
      ((homotopyEquivalence_iff_kanMapPiCriterion _).mpr h).isQCatEquivalence
    exact (isInvertibleEdge_congr (spaceInfinityEdgeValue_edge e)).mp he

variable {B : SSet.{u}}

/-- 元の余錐比較の頂点射を表す、端点を固定した実際の辺。 -/
def totalVertexComparisonEdge
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}) (c : JoinCocone F) :
    SpaceInfinity.{u}.Edge (coherentDiagramTotalCocone F).vertex c.vertex :=
  SSet.Edge.ofTruncated (Classical.choose (homotopyCategory_homMk_surjective
    (coherentDiagramTotalCocone F).vertex c.vertex (totalVertexComparison F c)))

/-- 選んだ辺は元の余錐全体からの比較射を表す。 -/
lemma totalVertexComparisonEdge_homMk
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}) (c : JoinCocone F) :
    SSet.Truncated.HomotopyCategory.homMk (totalVertexComparisonEdge F c).toTruncated =
      totalVertexComparison F c :=
  Classical.choose_spec (homotopyCategory_homMk_surjective
    (coherentDiagramTotalCocone F).vertex c.vertex (totalVertexComparison F c))

/-- 全空間から候補頂点への同じ比較を Kan 射として読む。 -/
def totalValueComparison
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}) (c : JoinCocone F) :
    spaceInfinityObject (coherentDiagramTotalCocone F).vertex ⟶
      spaceInfinityObject c.vertex :=
  spaceInfinityEdgeValue (totalVertexComparisonEdge F c)

/-- 元の余錐は余極限であることと、全空間比較の π₀・全基点正次数の全単射は同値。 -/
lemma isColimitCone_iff_totalPiCriterion
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}) (c : JoinCocone F) :
    IsColimitCone c ↔ KanMapPiCriterion (totalValueComparison F c) := by
  rw [isColimitCone_iff_totalVertexComparison_isIso]
  have h : IsIso (totalVertexComparison F c) ↔
      IsInvertibleEdge (totalVertexComparisonEdge F c) := by
    change IsIso (totalVertexComparison F c) ↔
      IsIso (SSet.Truncated.HomotopyCategory.homMk
        (totalVertexComparisonEdge F c).toTruncated)
    rw [totalVertexComparisonEdge_homMk]
  exact h.trans (spaceEdge_invertible_iff_piCriterion (totalVertexComparisonEdge F c))

end SerrePositivity.InfinityCategories.F2.PiCriterion
