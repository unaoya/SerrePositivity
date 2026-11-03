module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FunctorHomotopyPrismComparisonValues
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FunctorHomotopyPrismSpecifiedComponent
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FunctorHomotopyPrismNaturality

/-!
概要：始点も動く二つの元の実 prism の比較を、同じ native 始点と実終点の表示へ揃える。
方針：元の四頂点を厳密に回収し、同じ指定比較の端点表示だけを変更する。
規約：全係数・元の指定同型を保持。使われ方：F1 指定比較の型付き自然性の正方形。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {B C : SSet.{u + 1}} {F G : B ⟶ SpaceInfinity.{u}}
  (H : SSet.Homotopy F G) (p : C ⟶ B) (s t : C ⟶ leftUnstraightening F)
  (hs : s ≫ leftUnstraighteningProjection F = p) (ht : t ≫ leftUnstraighteningProjection F = p)
  (w : RelativeExtensionEndpointWitness pointedSpaceProjection
    ((Δ[1] ◁ p) ≫ functorSimplexDiagram (curry H.h)) (prismEndpoint 0 C)
    (s ≫ pullback.fst pointedSpaceProjection F) (prismEndpoint 1 C) G p)
  (w' : RelativeExtensionEndpointWitness pointedSpaceProjection
    ((Δ[1] ◁ p) ≫ functorSimplexDiagram (curry H.h)) (prismEndpoint 0 C)
    (t ≫ pullback.fst pointedSpaceProjection F) (prismEndpoint 1 C) G p)
local notation "d" => (Δ[1] ◁ p) ≫ functorSimplexDiagram (curry H.h)
local notation "x" => relativeFunctorVertex pointedSpaceProjection d
  (RelativeExtensionEndpointWitness.extension w) (RelativeExtensionEndpointWitness.over w)
local notation "y" => relativeFunctorVertex pointedSpaceProjection d
  (RelativeExtensionEndpointWitness.extension w') (RelativeExtensionEndpointWitness.over w')

/-- 始点も動く元の二実 prism の指定比較は、元の指定始域比較と厳密な可換正方形を作る。 -/
lemma functorHomotopyPrismSpecified_naturality (e : VertexIso x y) :
    functorHomotopyPrismNativeComparison H p s t hs ht w w' e ≪≫
      functorHomotopySourceEndpointIso H p t ht w' =
      functorHomotopySourceEndpointIso H p s hs w ≪≫
        functorHomotopyPrismActualComparison H p s t w w' e := by
  let f := functorHomotopyPrismSourceEvaluation H p ≫ HomotopyLimits.relativeFunctorPost
    (leftUnstraighteningProjection F) (leftUnstraighteningProjection G)
    (leftUnstraighteningMappingVertexMap F G (coherentVertexOfHomotopy H)).val
    (leftUnstraighteningMappingVertexMap F G (coherentVertexOfHomotopy H)).property p
  let r := functorHomotopyPrismTargetEvaluation H p
  let η := functorHomotopyPrismEndpointComparison H p
  exact vertexIso_square_of_heq (VertexIso.map e f) (η.app y) (η.app x) (VertexIso.map e r)
    (functorHomotopyPrismNativeComparison H p s t hs ht w w' e)
    (functorHomotopySourceEndpointIso H p t ht w')
    (functorHomotopySourceEndpointIso H p s hs w)
    (functorHomotopyPrismActualComparison H p s t w w' e)
    (functorHomotopyPrismNativeSource_vertex H p s hs w)
    (functorHomotopyPrismNativeSource_vertex H p t ht w')
    (functorHomotopyPrismTargetEvaluation_vertex H p s w)
    (functorHomotopyPrismTargetEvaluation_vertex H p t w')
    (vertexIsoOfEq_heq _ (functorHomotopyPrismNativeSource_vertex H p s hs w)
      (functorHomotopyPrismNativeSource_vertex H p t ht w')).symm
    (functorHomotopyPrismEndpointComparison_heq_specified H p t ht w')
    (functorHomotopyPrismEndpointComparison_heq_specified H p s hs w)
    (vertexIsoOfEq_heq _ (functorHomotopyPrismTargetEvaluation_vertex H p s w)
      (functorHomotopyPrismTargetEvaluation_vertex H p t w')).symm
    (functorHomotopyPrismEndpointComparison_naturality H p e)

end SerrePositivity.InfinityCategories.F2
