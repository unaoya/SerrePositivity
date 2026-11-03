module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitApexVertexCoefficientMaps
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitApexPointedFamilyComparison
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.SpaceSimplexPointedVertexBase

/-!
概要：元の普遍三角形の中間・終点を、同じ実余錐の fiber の元の輸送射へ戻す。
方針：元の二実面と長辺終点の厳密な式を、同じ頂点包含へ移す。
規約：元の普遍 prism・全係数・実 fiber を保持。使われ方：同じ全比較の終点評価。
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
local notation "s" => coherentColimitApexTriangle B T
local notation "q" => coherentColimitApexCoefficientMap B T
local notation "A" => spaceSimplexPointedCoefficients s
local notation "β" => fst Δ[2] A ≫ SSet.yonedaEquiv.symm s

/-- 元の全三角形の中間頂点の底は、元の実中間余錐頂点に厳密に定値。 -/
lemma coherentColimitApexPointedMiddle_base :
    simplexPrismVertex 2 1 A ≫ β = SSet.const (coherentDiagramTotalCocone G).vertex :=
  (spaceSimplexPointedVertex_base s 1).trans
    (congrArg SSet.const (coherentColimitApexMiddleCoefficient_vertex B T).symm)

/-- 元の全三角形の終頂点の底も、元の実終余錐頂点に厳密に定値。 -/
lemma coherentColimitApexPointedTarget_base :
    simplexPrismVertex 2 2 A ≫ β = SSet.const (coherentDiagramTotalCocone J).vertex :=
  (spaceSimplexPointedVertex_base s 2).trans
    (congrArg SSet.const (coherentColimitApexTargetCoefficient_vertex B T).symm)

/-- 元の普遍三角形の中間頂点は、同じ初点係数からの元の第一辺の普遍輸送。 -/
lemma coherentColimitApexPointedMiddle_endpoint :
    simplexPrismVertex 2 1 A ≫ coherentColimitRawUniversalTrianglePrism B T q =
      (q ≫ coherentColimitRawFiberTransport B a) ≫
        vertexFiberι pointedSpaceProjection (coherentDiagramTotalCocone G).vertex := by
  have hr : simplexPrismVertex 2 1 A =
      prismEndpoint 1 A ≫ (stdSimplex.δ (2 : Fin 3) ▷ A) := by
    apply SSet.hom_ext
    intro n
    rfl
  rw [hr, Category.assoc, coherentColimitRawUniversalTrianglePrism_first,
    coherentColimitRawTransportPointPrism_finish]

/-- 元の普遍三角形の終頂点は、元の二辺の同じ普遍輸送の合成射そのもの。 -/
lemma coherentColimitApexPointedTarget_endpoint :
    simplexPrismVertex 2 2 A ≫ coherentColimitRawUniversalTrianglePrism B T q =
      ((q ≫ coherentColimitRawFiberTransport B a) ≫ coherentColimitRawFiberTransport B b) ≫
        vertexFiberι pointedSpaceProjection (coherentDiagramTotalCocone J).vertex := by
  have hr : simplexPrismVertex 2 2 A =
      prismEndpoint 1 A ≫ (stdSimplex.δ (1 : Fin 3) ▷ A) := by
    apply SSet.hom_ext
    intro n
    rfl
  rw [hr, Category.assoc]
  exact coherentColimitRawUniversalTrianglePrism_long_finish B T q

end SerrePositivity.InfinityCategories.F2
