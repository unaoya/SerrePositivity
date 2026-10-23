module

public import SerrePositivity.InfinityCategories.F1.KanModels.KanEnrichedComparisonIndexTriangle

/-!
概要：既存の豊穣比較の辺そのものが合成三角形を持つ。
方針：三点添字の三角形を転置した共同評価で写し、三面の厳密な一致で戻す。
規約：同型な別の辺へ置き換えない。
使われ方：全対象の fiber transport の底の三角形に沿う合成則。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：二つの比較の実際の辺と合成比較の実際の辺は一つの合成三角形を持つ。
方針：三点図式の実現を転置して添字の三角形を写し、既存の三辺を回収する。
規約：端点も辺も構成済みのものをそのまま使う。
使われ方：切断による全対象の transport の合成を比較する。 -/
def kanEnrichedComparisonEdge_compStruct {C : Type (u + 1)} [Category.{u} C]
    [SimplicialCategory C] {F G H : EnrichedFunctor SSet.{u} C KanObject.{u}}
    (η : KanEnrichedComparison F G) (θ : KanEnrichedComparison G H) :
    SSet.Edge.CompStruct (kanEnrichedComparisonEdge η) (kanEnrichedComparisonEdge θ)
      (kanEnrichedComparisonEdge (η.trans θ)) := by
  let T := transposeFunctorFamily (kanEnrichedComparisonTriangleFamily η θ)
  refine (kanEnrichedComparisonIndexTriangle.map T).ofEq ?_ ?_ ?_
  · change (((SSet.uliftFunctor.{u + 1, u}).map
      (nerveMap kanEnrichedComparisonFirstIndex) ≫
        transposeFunctorFamily (kanEnrichedComparisonTriangleFamily η θ)).app
          (Opposite.op ⦋1⦌)) coherentResolutionComparisonIndexEdge.edge =
      (transposeFunctorFamily (kanEnrichedComparisonFamily η)).app
        (Opposite.op ⦋1⦌) coherentResolutionComparisonIndexEdge.edge
    rw [← transposeFunctorFamily_pre, kanEnrichedComparisonTriangleFamily_first]
  · change (((SSet.uliftFunctor.{u + 1, u}).map
      (nerveMap kanEnrichedComparisonSecondIndex) ≫
        transposeFunctorFamily (kanEnrichedComparisonTriangleFamily η θ)).app
          (Opposite.op ⦋1⦌)) coherentResolutionComparisonIndexEdge.edge =
      (transposeFunctorFamily (kanEnrichedComparisonFamily θ)).app
        (Opposite.op ⦋1⦌) coherentResolutionComparisonIndexEdge.edge
    rw [← transposeFunctorFamily_pre, kanEnrichedComparisonTriangleFamily_second]
  · change (((SSet.uliftFunctor.{u + 1, u}).map
      (nerveMap kanEnrichedComparisonLongIndex) ≫
        transposeFunctorFamily (kanEnrichedComparisonTriangleFamily η θ)).app
          (Opposite.op ⦋1⦌)) coherentResolutionComparisonIndexEdge.edge =
      (transposeFunctorFamily (kanEnrichedComparisonFamily (η.trans θ))).app
        (Opposite.op ⦋1⦌) coherentResolutionComparisonIndexEdge.edge
    rw [← transposeFunctorFamily_pre, kanEnrichedComparisonTriangleFamily_long]

/-- 概要：豊穣比較の実現は関手空間の射として実際の合成を保つ。
方針：構成した同じ三辺の合成三角形の関係を使う。
規約：成分での等式から大域的な等式を推測しない。
使われ方：大域的な始点評価の逆を使う transport の合成計算。 -/
lemma kanEnrichedComparisonEdge_hom_trans {C : Type (u + 1)} [Category.{u} C]
    [SimplicialCategory C] {F G H : EnrichedFunctor SSet.{u} C KanObject.{u}}
    (η : KanEnrichedComparison F G) (θ : KanEnrichedComparison G H) :
    SSet.Truncated.HomotopyCategory.homMk (kanEnrichedComparisonEdge η) ≫
        SSet.Truncated.HomotopyCategory.homMk (kanEnrichedComparisonEdge θ) =
      SSet.Truncated.HomotopyCategory.homMk (kanEnrichedComparisonEdge (η.trans θ)) :=
  SSet.Truncated.HomotopyCategory.homMk_comp_homMk
    (kanEnrichedComparisonEdge_compStruct η θ).toTruncated

end SerrePositivity.InfinityCategories
