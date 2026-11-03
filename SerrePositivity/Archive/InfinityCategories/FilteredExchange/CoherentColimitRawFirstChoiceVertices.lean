module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitRawFirstChoicePrism
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitConstantTransportPointPrism

/-!
概要：元の定値第一辺と同じ raw 普遍第一辺を、同じ全初期値固定の選択空間へ入れる。
方針：元の二実 prism の始点と底をそのまま使う。
規約：二辺を選び直さない。使われ方：全選択空間の自然性を元の二つの指定比較へ戻す。
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
  {F G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}} (a : SSet.Homotopy F G)

/-- 元の第一辺の実 prism を、元の同じ初期値と実底の選択空間へ入れる。 -/
def coherentColimitRawFirstChoiceVertex {K : SSet.{u + 1}}
    (f : K ⟶ vertexFiber pointedSpaceProjection (JoinCocone.vertex (coherentDiagramTotalCocone F)))
    (W : (Δ[1] : SSet.{u + 1}) ⊗ K ⟶ PointedSpaceInfinity.{u})
    (hp : W ≫ pointedSpaceProjection = fst (Δ[1] : SSet.{u + 1}) K ≫
      SSet.yonedaEquiv.symm (coherentColimitFunctorEdge B a).edge)
    (hs : prismEndpoint 0 K ≫ W = f ≫ vertexFiberι pointedSpaceProjection
      (JoinCocone.vertex (coherentDiagramTotalCocone F))) :
    (coherentColimitRawFirstChoiceSpace B a f) _⦋0⦌ :=
  relativeFunctorExtensionSpaceVertexEquiv pointedSpaceProjection _ (prismEndpoint 0 K) _
    (coherentColimitRawFirstChoice_initial_base B a f) ⟨W, hp, hs⟩

/-- 元の同じ raw 普遍第一辺を、元の全第一辺の選択空間の頂点として保持する。 -/
def coherentColimitRawFirstChoiceUniversalVertex {K : SSet.{u + 1}}
    (f : K ⟶ vertexFiber pointedSpaceProjection
      (JoinCocone.vertex (coherentDiagramTotalCocone F))) :
    (coherentColimitRawFirstChoiceSpace B a f) _⦋0⦌ :=
  coherentColimitRawFirstChoiceVertex B a f (coherentColimitRawTransportPointPrism B a f)
    (coherentColimitRawTransportPointPrism_projection B a f)
    (coherentColimitRawTransportPointPrism_start B a f)

/-- 元の定値第一辺の同じ選択済み prism を、同じ全初期値固定の選択空間へ入れる。 -/
def coherentColimitRawFirstChoiceConstantVertex :
    (coherentColimitRawFirstChoiceSpace B a
      (coherentColimitRawConstantFiberProjection B F)) _⦋0⦌ :=
  coherentColimitRawFirstChoiceVertex B a (coherentColimitRawConstantFiberProjection B F)
    (functorHomotopyPointedPrism
      (simplicialHomotopyOfFunctorEdge (coherentColimitConstantEdge B a)) (𝟙 _))
    (by
      rw [functorHomotopyPointedPrism_projection, Category.id_comp]
      exact coherentColimitConstantPrism_base B a _)
    (by
      rw [functorHomotopyPointedPrism_source, Category.id_comp]
      exact (constantUnstraighteningFiberProjection_ι _ _).symm)

end SerrePositivity.InfinityCategories.F2
