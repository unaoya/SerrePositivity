module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitRawFirstChoiceVertexEvaluation

/-!
概要：元の定値第一辺の実 prism データと、二実第一辺の全終点評価の値を保持する。
方針：元の prism の実両端を計算し、同じ全評価の実頂点公式へ入力する。
規約：端点は実射から回収する。使われ方：元の第一辺比較の後合成と全族交換式の反映。
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
local notation "P" => coherentColimitRawConstantFiberProjection B F
local notation "PG" => coherentColimitRawConstantFiberProjection B G
local notation "ca" => simplicialHomotopyOfFunctorEdge (coherentColimitConstantEdge B a)
local notation "W" => functorHomotopyPointedPrism ca (𝟙 _)
local notation "ma" => Subtype.val (leftUnstraighteningMappingVertexMap _ _
  (coherentVertexOfHomotopy ca))

/-- 元の定値第一辺の実 prism は、元の同じ第一辺の実底を被覆する。 -/
lemma coherentColimitRawFirstConstantPrism_projection :
    W ≫ pointedSpaceProjection = fst (Δ[1] : SSet.{u + 1}) _ ≫
      SSet.yonedaEquiv.symm (coherentColimitFunctorEdge B a).edge := by
  rw [functorHomotopyPointedPrism_projection, Category.id_comp]
  exact coherentColimitConstantPrism_base B a _

/-- 元の定値第一辺の実 prism の始点は、元の同じ raw fiber 射影。 -/
lemma coherentColimitRawFirstConstantPrism_start :
    prismEndpoint 0 _ ≫ W = P ≫ vertexFiberι pointedSpaceProjection
      (JoinCocone.vertex (coherentDiagramTotalCocone F)) := by
  rw [functorHomotopyPointedPrism_source, Category.id_comp]
  exact (constantUnstraighteningFiberProjection_ι _ _).symm

/-- 元の定値第一辺の実 prism の終点は、元の同じ第一作用後の raw fiber 射影。 -/
lemma coherentColimitRawFirstConstantPrism_finish :
    prismEndpoint 1 _ ≫ W = (ma ≫ PG) ≫ vertexFiberι pointedSpaceProjection
      (JoinCocone.vertex (coherentDiagramTotalCocone G)) := by
  rw [functorHomotopyPointedPrism_target, Category.id_comp]
  simp only [Category.assoc, coherentColimitRawConstantFiberProjection,
    constantUnstraighteningFiberProjection_ι]

/-- 全第一辺終点評価の元の定値辺での値は、元の同じ第一作用後の射影の関手頂点。 -/
lemma coherentColimitRawFirstChoiceEndpoint_constant_vertex :
    (curry (coherentColimitRawFirstChoiceEndpoint B a P)).app (Opposite.op ⦋0⦌)
      (coherentColimitRawFirstChoiceConstantVertex B a) = functorVertex (ma ≫ PG) :=
  coherentColimitRawFirstChoiceEndpoint_vertex B a P W
    (coherentColimitRawFirstConstantPrism_projection B a)
    (coherentColimitRawFirstConstantPrism_start B a) (ma ≫ PG)
    (coherentColimitRawFirstConstantPrism_finish B a)

/-- 全第一辺終点評価の元の普遍辺での値は、元の同じ raw 普遍輸送の関手頂点。 -/
lemma coherentColimitRawFirstChoiceEndpoint_universal_vertex :
    (curry (coherentColimitRawFirstChoiceEndpoint B a P)).app (Opposite.op ⦋0⦌)
      (coherentColimitRawFirstChoiceUniversalVertex B a P) =
        functorVertex (P ≫ coherentColimitRawFiberTransport B a) :=
  coherentColimitRawFirstChoiceEndpoint_vertex B a P (coherentColimitRawTransportPointPrism B a P)
    (coherentColimitRawTransportPointPrism_projection B a P)
    (coherentColimitRawTransportPointPrism_start B a P) (P ≫ coherentColimitRawFiberTransport B a)
    (coherentColimitRawTransportPointPrism_finish B a P)

end SerrePositivity.InfinityCategories.F2
