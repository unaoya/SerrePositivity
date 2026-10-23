module

public import SerrePositivity.InfinityCategories.HomotopyLimits.SiftedCoherentProductComparison
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.EdgeApexPrism
public import SerrePositivity.InfinityCategories.F1.Coherent.KanInvertible

/-!
概要：coherent 積図式の元の余極限比較を、同じ辺を保つ頂点円柱にする。
方針：具体的 Kan 射を既存の元の Kan 対象間の辺にする。
規約：sifted 性は可逆性だけに使う。使われ方：native な二項積錐の頂点輸送。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
variable {B : SSet.{u}}
  (F G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})

/-- 元の余極限 Kan 比較を、元の Kan 対象間の射として束縛する。 -/
def coherentProductTotalKanMap :
    F2.coherentDiagramTotalKanObject (coherentSpaceTensorProduct F G) ⟶
      (kanTensorLeft (F2.coherentDiagramTotalKanObject F)).obj
        (F2.coherentDiagramTotalKanObject G) := coherentProductTotalKanComparison F G

/-- 元の比較辺の全一単体を保つ、余極限頂点の円柱。 -/
def coherentProductComparisonApexPrism :
    (Δ[1] : SSet.{u + 1}) ⊗ (Δ[0] : SSet.{u + 1}) ⟶ SpaceInfinity.{u} :=
  F2.edgeApexPrism (coherentNerveEdge (coherentProductTotalKanMap F G))

/-- 頂点円柱の始点は、積図式の元の余極限頂点。 -/
lemma coherentProductComparisonApexPrism_zero :
    prismEndpoint 0 (Δ[0] : SSet.{u + 1}) ≫ coherentProductComparisonApexPrism F G =
      SSet.yonedaEquiv.symm (F2.coherentDiagramTotalVertex (coherentSpaceTensorProduct F G)) := by
  rw [coherentProductComparisonApexPrism, F2.edgeApexPrism_zero,
    F2.coherentDiagramTotalVertex, spaceInfinityVertex_eq_coherent]

/-- 頂点円柱の終点は、二つの元の余極限 Kan 模型の積。 -/
lemma coherentProductComparisonApexPrism_one :
    prismEndpoint 1 (Δ[0] : SSet.{u + 1}) ≫ coherentProductComparisonApexPrism F G =
      SSet.yonedaEquiv.symm (coherentNerveVertex
        ((kanTensorLeft (F2.coherentDiagramTotalKanObject F)).obj
          (F2.coherentDiagramTotalKanObject G))) := F2.edgeApexPrism_one _

/-- sifted な底上で、同じ元の比較辺の円柱の全垂直辺は可逆。 -/
lemma coherentProductComparisonApexPrism_vertical_isInvertible [IsSiftedInfinity B]
    (x : (Δ[0] : SSet.{u + 1}) _⦋0⦌) :
    IsInvertibleEdge (edgeOfSimplex ((coherentProductComparisonApexPrism F G).app
      (Opposite.op ⦋1⦌) (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u + 1})),
        PinchedHom.constant x 1))) := by
  have := kanTensor_isKan (F2.coherentDiagramTotalKan F) (F2.coherentDiagramTotalKan G)
  exact F2.edgeApexPrism_vertical_isInvertible _
    (coherentKanEdge_isInvertible_of_isQCatEquivalence
      (coherentProductTotalKanComparison_homotopyEquivalence F G).isQCatEquivalence) x

end SerrePositivity.InfinityCategories.HomotopyLimits
