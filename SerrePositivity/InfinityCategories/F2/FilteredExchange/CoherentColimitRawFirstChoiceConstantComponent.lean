module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentColimitRawFirstChoiceComponentTransport
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentColimitRawLastLongRemainder

/-!
概要：全第一辺比較の元の定値第一辺成分を、元の新長辺残余の指定値へ同定する。
方針：元の定値第一辺と最後辺普遍輸送を全三角形へ戻し、二辺固定の比較を消去する。
規約：元の指定二単体・選択済み prism・残余を保持。使われ方：元の三因子模型式の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable (B : SSet.{u})
  {F G J : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}}
  {a : SSet.Homotopy F G} {b : SSet.Homotopy G J} {d : SSet.Homotopy F J}
  (T : FunctorCompositionTriangle a b d)
local notation "P" => coherentColimitRawConstantFiberProjection B F
local notation "PG" => coherentColimitRawConstantFiberProjection B G
local notation "ca" => simplicialHomotopyOfFunctorEdge (coherentColimitConstantEdge B a)
local notation "W" => functorHomotopyPointedPrism ca (𝟙 _)
local notation "ma" => Subtype.val (leftUnstraighteningMappingVertexMap _ _
  (coherentVertexOfHomotopy ca))
local notation "Y" => coherentColimitTriangleRawLastPrism B T

/-- 元の定値第一辺の全比較成分は、同じ新長辺残余の指定比較そのもの。 -/
lemma coherentColimitRawFirstChoiceTriangleComparisonApp_constant_heq :
    HEq (coherentColimitRawFirstChoiceTriangleComparisonApp B T P
      (coherentColimitRawFirstChoiceConstantVertex B a))
      (coherentColimitRawLastLongRemainderIso B T) := by
  have hp : W ≫ pointedSpaceProjection = fst (Δ[1] : SSet.{u + 1}) _ ≫
      SSet.yonedaEquiv.symm (coherentColimitFunctorEdge B a).edge := by
    rw [functorHomotopyPointedPrism_projection, Category.id_comp]
    exact coherentColimitConstantPrism_base B a _
  have hs : prismEndpoint 0 _ ≫ W = P ≫ vertexFiberι pointedSpaceProjection
      (JoinCocone.vertex (coherentDiagramTotalCocone F)) := by
    rw [functorHomotopyPointedPrism_source, Category.id_comp]
    exact (constantUnstraighteningFiberProjection_ι _ _).symm
  have hg : prismEndpoint 1 _ ≫ W = (ma ≫ PG) ≫ vertexFiberι pointedSpaceProjection
      (JoinCocone.vertex (coherentDiagramTotalCocone G)) := by
    rw [functorHomotopyPointedPrism_target, Category.id_comp]
    simp only [Category.assoc, coherentColimitRawConstantFiberProjection,
      constantUnstraighteningFiberProjection_ι]
  have hY := (coherentColimitTriangleRawLastPrism_projection B T).trans
    (coherentColimitConstantTriangle_base B T _)
  have hfirst : (stdSimplex.δ (2 : Fin 3) ▷ _) ≫ Y = W := by
    simpa only [coherentColimitRawConstantDiagram] using
      coherentColimitTriangleRawLastPrism_first B T
  have hlast : (stdSimplex.δ (0 : Fin 3) ▷ _) ≫ Y =
      coherentColimitRawTransportPointPrism B b (ma ≫ PG) := by
    simpa only [coherentColimitRawConstantDiagram] using
      coherentColimitTriangleRawLastPrism_last B T
  have hh := coherentColimitRawFirstChoiceTriangleComparisonApp_heq_transport B T P
    W hp hs (ma ≫ PG) hg Y hY hfirst hlast (coherentColimitTriangleRawLastLongTransport B T)
    (coherentColimitTriangleRawLastLongTransport_point_prism B T
      (stdSimplex.obj₀Equiv.symm (0 : Fin 1)))
  exact hh.trans (functorIsoOfEq_heq _ _ _).symm

end SerrePositivity.InfinityCategories.F2
