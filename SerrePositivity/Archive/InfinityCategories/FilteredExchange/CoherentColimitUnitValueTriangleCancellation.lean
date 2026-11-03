module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitUnitValueActionCoherence
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.IsoFiveFactorCancellation

/-!
概要：元の五因子の全族の整合式から、元の定値三角形因子をその逆で消去する。
方針：同じ指定三角形因子の逆を元の式の左から合成する。
規約：全係数・元の指定値・元の単位を保持。使われ方：下側輸送因子の消去。
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

/-- 元の定値三角形の逆を元の全族の式へ合成すると、元の残り二因子が残る。 -/
lemma coherentColimitUnitValueAction_triangle_cancel :
    ((VertexIso.map
      ((functorTriangleSequentialPostComparison (coherentColimitConstantTriangle B T) p).app
        ((functorHomotopyRelativePost u₀ p).app _ x₀)) Q).symm ≪≫
      coherentColimitUnitValueAction B d p x₀) ≪≫
        VertexIso.map (VertexIso.map ((functorTriangleSequentialPostComparison T p).app x₀)
          (functorHomotopyRelativePost u₃ p)) Q =
      VertexIso.map (VertexIso.map (coherentColimitUnitValueComparison B l p x₀)
        (functorHomotopyRelativePost rc p)) Q ≪≫
        coherentColimitUnitValueAction B r p ((functorHomotopyRelativePost l p).app _ x₀) := by
  exact iso_five_factor_cancel_prefix _ _ _ _ _ (coherentColimitUnitValueAction_coherence B T)

end SerrePositivity.InfinityCategories.F2
