module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.SpaceTriangleSourceConeVertices
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.SpaceSimplexPointedFamilyVertex
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.SpaceSimplexPointedFamilyInitial
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.PointedCoherentFixedHomComposition

/-!
概要：元の全 Space 三角形上の pointed 族の三頂点を、元の全係数の作用で計算する。
方針：元の初点の標準比較と、第一・長辺の固定 Kan 射による同じ後合成を回収する。
規約：一般 coherent 三角形と全反転 Hom 係数を保持。
使われ方：元の三辺の値比較と指定 path の同時照合。
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
variable (s : SpaceInfinity.{u} _⦋2⦌)

/-- 元の全 pointed 三角形の初点作用は、同じ元の標準 fiber 比較そのもの。 -/
lemma spaceTrianglePointedFamily_source_action :
    simplexPrismVertex 2 0 (spaceSimplexPointedCoefficients s) ≫ spaceSimplexPointedFamily s =
      pointedCoherentFiberComparison (s.obj ⟨ULift.up 0⟩) ≫
        vertexFiberι pointedSpaceProjection (coherentNerveVertex (s.obj ⟨ULift.up 0⟩)) :=
  spaceSimplexPointedFamily_initial s

/-- 元の中間頂点の作用は、元の同じ第一辺による全反転 Hom の後合成。 -/
lemma spaceTrianglePointedFamily_middle_action :
    simplexPrismVertex 2 1 (spaceSimplexPointedCoefficients s) ≫ spaceSimplexPointedFamily s =
    (SSet.uliftFunctor.{u + 1, u}).map (SSet.opFunctor.map
      (eHomWhiskerLeft SSet pointKanObject (coherentEdgeHom (SpaceInfinity.δ 2 s)))) ≫
        pointedCoherentFiberComparison (s.obj ⟨ULift.up 1⟩) ≫
          vertexFiberι pointedSpaceProjection (coherentNerveVertex (s.obj ⟨ULift.up 1⟩)) := by
  rw [spaceSimplexPointedFamily_vertex, spaceTriangleSourceCone_middle_vertex]
  exact pointedCoherentSourcePrecomposition_fixed (coherentEdgeHom (SpaceInfinity.δ 2 s))

/-- 元の終頂点の作用は、元の同じ長辺による全反転 Hom の後合成。 -/
lemma spaceTrianglePointedFamily_target_action :
    simplexPrismVertex 2 2 (spaceSimplexPointedCoefficients s) ≫ spaceSimplexPointedFamily s =
    (SSet.uliftFunctor.{u + 1, u}).map (SSet.opFunctor.map
      (eHomWhiskerLeft SSet pointKanObject (coherentEdgeHom (SpaceInfinity.δ 1 s)))) ≫
        pointedCoherentFiberComparison (s.obj ⟨ULift.up 2⟩) ≫
          vertexFiberι pointedSpaceProjection (coherentNerveVertex (s.obj ⟨ULift.up 2⟩)) := by
  rw [spaceSimplexPointedFamily_vertex, spaceTriangleSourceCone_target_vertex]
  exact pointedCoherentSourcePrecomposition_fixed (coherentEdgeHom (SpaceInfinity.δ 1 s))

end SerrePositivity.InfinityCategories.F2
