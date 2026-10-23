module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentColimitUnitValueAction
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentColimitUnitTriangleValueCoherence
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.VertexIsoTriangleRelationMap

/-!
概要：元の単位三角柱の整合式全体を、元の標的余錐の値へ写す。
方針：同じ相対 Hom の値への作用により、指定値の逆・合成・後合成を保つ。
規約：全三角形・二面・指定値を保持。使われ方：外側因子を消去して a6 の整合へ反映する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
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
local notation "Q" => Iso.hom (constantUnstraighteningRelativeIso p
  (JoinCocone.vertex (coherentDiagramTotalCocone J))) ≫
    CategoryTheory.Functor.map (ihom (leftUnstraightening F))
      (QCatEquivalence.hom (pointedSpaceFiberValueEquivalence
        (JoinCocone.vertex (coherentDiagramTotalCocone J))))

/-- 元の全三角形の二面比較の整合式は、元の標的の値でも同じ指定五因子を保つ。 -/
lemma coherentColimitUnitValueAction_coherence :
    coherentColimitUnitValueAction B d p x₀ ≪≫
        VertexIso.map (VertexIso.map ((functorTriangleSequentialPostComparison T p).app x₀)
          (functorHomotopyRelativePost u₃ p)) Q =
      VertexIso.map
          ((functorTriangleSequentialPostComparison (coherentColimitConstantTriangle B T) p).app
            ((functorHomotopyRelativePost u₀ p).app _ x₀)) Q ≪≫
        VertexIso.map (VertexIso.map (coherentColimitUnitValueComparison B l p x₀)
          (functorHomotopyRelativePost rc p)) Q ≪≫
        coherentColimitUnitValueAction B r p ((functorHomotopyRelativePost l p).app _ x₀) := by
  exact vertexIso_five_factor_relation_map Q
    (coherentColimitUnitValueComparison B d p x₀)
    (VertexIso.map ((functorTriangleSequentialPostComparison T p).app x₀)
      (functorHomotopyRelativePost u₃ p))
    ((functorTriangleSequentialPostComparison (coherentColimitConstantTriangle B T) p).app
      ((functorHomotopyRelativePost u₀ p).app _ x₀))
    (VertexIso.map (coherentColimitUnitValueComparison B l p x₀)
      (functorHomotopyRelativePost rc p))
    (coherentColimitUnitValueComparison B r p ((functorHomotopyRelativePost l p).app _ x₀))
    (coherentColimitUnitTriangleValue_coherence B T)

end SerrePositivity.InfinityCategories.F2
