module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitApexCoefficientMap
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.SpaceTrianglePointedVertexActions

/-!
概要：明示した全 pointed 三角形の中間・終点作用を、元の実余錐の fiber に移す。
方針：元の第一・長辺の全反転 Hom 作用に、同じ実頂点の等式だけを合成する。
規約：元の係数と実 fiber を保持。使われ方：同じ全比較の native 終点同型。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
open HomotopyLimits
variable (B : SSet.{u})
  {F G J : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}}
  {a : SSet.Homotopy F G} {b : SSet.Homotopy G J} {d : SSet.Homotopy F J}
  (T : FunctorCompositionTriangle a b d)
local notation "s" => coherentColimitApexTriangle B T
local notation "K₁" => EnrichedFunctor.obj s (SimplicialThickening.mk (ULift.up 1))
local notation "K₂" => EnrichedFunctor.obj s (SimplicialThickening.mk (ULift.up 2))

/-- 元の実中間余錐頂点と同じ三角形の中間対象の coherent 表示の等式。 -/
lemma coherentColimitApexMiddleCoefficient_vertex :
    (coherentDiagramTotalCocone G).vertex = coherentNerveVertex K₁ :=
  (coherentColimitApex_raw_one_vertex B T).trans (spaceInfinityVertex_eq_coherent K₁)

/-- 元の実終余錐頂点と同じ三角形の終対象の coherent 表示の等式。 -/
lemma coherentColimitApexTargetCoefficient_vertex :
    (coherentDiagramTotalCocone J).vertex = coherentNerveVertex K₂ :=
  (coherentColimitApex_raw_two_vertex B T).trans (spaceInfinityVertex_eq_coherent K₂)

/-- 元の全初点係数を、元の第一辺で元の実中間 fiber へ写す。 -/
def coherentColimitApexMiddleCoefficientMap : spaceSimplexPointedCoefficients s ⟶
    vertexFiber pointedSpaceProjection (coherentDiagramTotalCocone G).vertex :=
  (SSet.uliftFunctor.{u + 1, u}).map (SSet.opFunctor.map
    (eHomWhiskerLeft SSet pointKanObject (coherentEdgeHom (SpaceInfinity.δ 2 s)))) ≫
      pointedCoherentFiberComparison K₁ ≫ eqToHom (congrArg (vertexFiber pointedSpaceProjection)
        (coherentColimitApexMiddleCoefficient_vertex B T).symm)

/-- 元の全初点係数を、元の長辺で元の実終 fiber へ写す。 -/
def coherentColimitApexTargetCoefficientMap : spaceSimplexPointedCoefficients s ⟶
    vertexFiber pointedSpaceProjection (coherentDiagramTotalCocone J).vertex :=
  (SSet.uliftFunctor.{u + 1, u}).map (SSet.opFunctor.map
    (eHomWhiskerLeft SSet pointKanObject (coherentEdgeHom (SpaceInfinity.δ 1 s)))) ≫
      pointedCoherentFiberComparison K₂ ≫ eqToHom (congrArg (vertexFiber pointedSpaceProjection)
        (coherentColimitApexTargetCoefficient_vertex B T).symm)

/-- 元の中間 fiber への全係数射は、明示した同じ全 pointed 族の中間頂点そのもの。 -/
lemma coherentColimitApexMiddleCoefficientMap_ι :
    coherentColimitApexMiddleCoefficientMap B T ≫
      vertexFiberι pointedSpaceProjection (coherentDiagramTotalCocone G).vertex =
    simplexPrismVertex 2 1 (spaceSimplexPointedCoefficients s) ≫ spaceSimplexPointedFamily s := by
  rw [coherentColimitApexMiddleCoefficientMap]
  simp only [Category.assoc]
  rw [vertexFiberTransport_ι pointedSpaceProjection
    (coherentColimitApexMiddleCoefficient_vertex B T).symm]
  exact (spaceTrianglePointedFamily_middle_action s).symm

/-- 元の終 fiber への全係数射も、明示した同じ全 pointed 族の終頂点そのもの。 -/
lemma coherentColimitApexTargetCoefficientMap_ι :
    coherentColimitApexTargetCoefficientMap B T ≫
      vertexFiberι pointedSpaceProjection (coherentDiagramTotalCocone J).vertex =
    simplexPrismVertex 2 2 (spaceSimplexPointedCoefficients s) ≫ spaceSimplexPointedFamily s := by
  rw [coherentColimitApexTargetCoefficientMap]
  simp only [Category.assoc]
  rw [vertexFiberTransport_ι pointedSpaceProjection
    (coherentColimitApexTargetCoefficient_vertex B T).symm]
  exact (spaceTrianglePointedFamily_target_action s).symm

end SerrePositivity.InfinityCategories.F2
