module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentColimitUnitFirstTotalRelation
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentColimitUnitMiddleTotalRelation
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentColimitUnitLastTotalRelation
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentColimitUnitValueComparison
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.ThreeTriangleIsoCancellation

/-!
概要：元の単位三角柱の三関係から内部面を消去し、指定三角形と元の単位比較の整合を得る。
方針：同じ全空間上の三関係を指定同型の相殺式へ適用する。
規約：元の上下二面・指定対角・指定値を保持。使われ方：二三角形・指定 path の全錐比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable (B : SSet.{u})
  {F G J : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}}
  {l : SSet.Homotopy F G} {r : SSet.Homotopy G J} {d : SSet.Homotopy F J}
  (T : FunctorCompositionTriangle l r d)
local notation "p" => leftUnstraighteningProjection F
local notation "x₀" => relativeFunctorVertex p p (𝟙 (leftUnstraightening F)) (Category.id_comp p)
local notation "u₀" => coconeTransformationHomotopy (coherentDiagramTotalCocone F)
local notation "u₃" => coconeTransformationHomotopy (coherentDiagramTotalCocone J)
local notation "rc" => simplicialHomotopyOfFunctorEdge (coherentColimitConstantEdge B r)

/-- 元の単位三角柱の二内部面を消去した、元の指定比較と全三角形の厳密な整合式。 -/
lemma coherentColimitUnitTriangleValue_coherence :
    coherentColimitUnitValueComparison B d p x₀ ≪≫
        VertexIso.map ((functorTriangleSequentialPostComparison T p).app x₀)
          (functorHomotopyRelativePost u₃ p) =
      (functorTriangleSequentialPostComparison (coherentColimitConstantTriangle B T) p).app
          ((functorHomotopyRelativePost u₀ p).app _ x₀) ≪≫
        VertexIso.map (coherentColimitUnitValueComparison B l p x₀)
          (functorHomotopyRelativePost rc p) ≪≫
        coherentColimitUnitValueComparison B r p ((functorHomotopyRelativePost l p).app _ x₀) := by
  have h := threeTriangleIso_cancel
    ((functorTriangleSequentialPostComparison (coherentColimitUnitLowerTriangle B d) p).app x₀)
    ((functorTriangleSequentialPostComparison (coherentColimitUnitUpperTriangle B d) p).app x₀)
    ((functorTriangleSequentialPostComparison (coherentColimitConstantTriangle B T) p).app
      ((functorHomotopyRelativePost u₀ p).app _ x₀))
    (VertexIso.map ((functorTriangleSequentialPostComparison T p).app x₀)
      (functorHomotopyRelativePost u₃ p))
    ((functorTriangleSequentialPostComparison (coherentColimitUnitInteriorLast B T) p).app x₀)
    ((functorTriangleSequentialPostComparison (coherentColimitUnitInteriorFirst B T) p).app x₀)
    (VertexIso.map
      ((functorTriangleSequentialPostComparison (coherentColimitUnitLowerTriangle B l) p).app x₀)
      (functorHomotopyRelativePost rc p))
    (VertexIso.map
      ((functorTriangleSequentialPostComparison (coherentColimitUnitUpperTriangle B l) p).app x₀)
      (functorHomotopyRelativePost rc p))
    ((functorTriangleSequentialPostComparison (coherentColimitUnitLowerTriangle B r) p).app
      ((functorHomotopyRelativePost l p).app _ x₀))
    ((functorTriangleSequentialPostComparison (coherentColimitUnitUpperTriangle B r) p).app
      ((functorHomotopyRelativePost l p).app _ x₀))
    (coherentColimitUnitFirstTotalRelation B T) (coherentColimitUnitMiddleTotalRelation B T)
    (coherentColimitUnitLastTotalRelation B T)
  simpa only [coherentColimitUnitValueComparison, vertexIso_map_trans, vertexIso_map_symm] using h

end SerrePositivity.InfinityCategories.F2
