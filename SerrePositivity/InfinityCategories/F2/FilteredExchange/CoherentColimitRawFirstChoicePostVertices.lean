module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentColimitRawFirstConstantVertexData

/-!
概要：全第一辺終点を任意の実射で写した後の二実頂点を計算する。
方針：内部 Hom の作用と元の終点評価式を使う。
規約：頂点等式は実射の計算から得る。使われ方：全長辺比較の合成の指定値への反映。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable (B : SSet.{u})
  {F G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}} (a : SSet.Homotopy F G)
  {X : SSet.{u + 1}} (t : vertexFiber pointedSpaceProjection
    (JoinCocone.vertex (coherentDiagramTotalCocone G)) ⟶ X)
local notation "P" => coherentColimitRawConstantFiberProjection B F
local notation "PG" => coherentColimitRawConstantFiberProjection B G
local notation "K" => leftUnstraightening (coherentColimitRawConstantDiagram B F)
local notation "ca" => simplicialHomotopyOfFunctorEdge (coherentColimitConstantEdge B a)
local notation "ma" => Subtype.val (leftUnstraighteningMappingVertexMap _ _
  (coherentVertexOfHomotopy ca))

/-- 全第一辺終点の後合成の定値第一辺での実頂点。 -/
lemma coherentColimitRawFirstChoiceEndpoint_post_constant_vertex :
    ((ihom K).map t).app (Opposite.op ⦋0⦌)
      ((curry (coherentColimitRawFirstChoiceEndpoint B a P)).app (Opposite.op ⦋0⦌)
        (coherentColimitRawFirstChoiceConstantVertex B a)) =
      functorVertex ((ma ≫ PG) ≫ t) := by
  rw [coherentColimitRawFirstChoiceEndpoint_constant_vertex]
  rfl

/-- 全第一辺終点の後合成の普遍第一辺での実頂点。 -/
lemma coherentColimitRawFirstChoiceEndpoint_post_universal_vertex :
    ((ihom K).map t).app (Opposite.op ⦋0⦌)
      ((curry (coherentColimitRawFirstChoiceEndpoint B a P)).app (Opposite.op ⦋0⦌)
        (coherentColimitRawFirstChoiceUniversalVertex B a P)) =
      functorVertex ((P ≫ coherentColimitRawFiberTransport B a) ≫ t) := by
  rw [coherentColimitRawFirstChoiceEndpoint_universal_vertex]
  rfl

end SerrePositivity.InfinityCategories.F2
