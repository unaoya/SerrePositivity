module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.FunctorHomotopyPrismNativeVertex
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.VertexIsoEndpointTransport

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

/-- 元の prism 比較の始点像に native 作用を施した、同じ元の指定値。 -/
def functorHomotopyPrismNativeComparison (e : VertexIso x y) :=
  vertexIsoOfEq (VertexIso.map e (functorHomotopyPrismSourceEvaluation H p ≫
    HomotopyLimits.relativeFunctorPost (leftUnstraighteningProjection F)
      (leftUnstraighteningProjection G)
      (leftUnstraighteningMappingVertexMap F G (coherentVertexOfHomotopy H)).val
      (leftUnstraighteningMappingVertexMap F G (coherentVertexOfHomotopy H)).property p))
    (functorHomotopyPrismNativeSource_vertex H p s hs w)
    (functorHomotopyPrismNativeSource_vertex H p t ht w')

/-- 元の prism 比較の終点像を、元の二つの実終点の表示へ厳密に揃えた値。 -/
def functorHomotopyPrismActualComparison (e : VertexIso x y) :=
  vertexIsoOfEq (VertexIso.map e (functorHomotopyPrismTargetEvaluation H p))
    (functorHomotopyPrismTargetEvaluation_vertex H p s w)
    (functorHomotopyPrismTargetEvaluation_vertex H p t w')

end SerrePositivity.InfinityCategories.F2
