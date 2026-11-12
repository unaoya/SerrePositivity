module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.PointedPrismFamilyComparison
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.RelativeFunctorExtensionEndpoint

/-!
概要：全パラメータ固定の pointed 三角形の選択空間を、元の三辺の相対関手空間へ制限。
方針：同じ延長を含めて元の辺で前合成し、全実延長の辺の値を回収する。
規約：第零辺も含む三辺すべて。使われ方：一つの全族比較の三つの指定辺比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 三角形の長辺と最後の辺の終点は、同じ元の最終頂点に全パラメータで一致する。 -/
lemma triangleFamilyEdge_terminal (E K : SSet.{u + 1}) (j : Fin 3) (hj : j ≠ 2) :
    (prismEndpoint 1 E ▷ K) ≫ ((stdSimplex.δ j ▷ E) ▷ K) =
      simplexPrismVertex 2 2 E ▷ K := by
  have ht : prismEndpoint 1 E ≫ (stdSimplex.δ j ▷ E) = simplexPrismVertex 2 2 E := by
    fin_cases j
    · rfl
    · rfl
    · exact (hj rfl).elim
  rw [← comp_whiskerRight, ht]

variable {E B K : SSet.{u + 1}} {p : E ⟶ B}
  (D : PointedTransportPrismFamily (K := K) (scaffoldFirstVertex 2) p)
local notation "b₂" => ((Δ[2] ◁ p) ▷ K) ≫ PointedTransportPrismFamily.diagram D

/-- 元の全三角形の実延長を、元の同じ全辺へ制限する。 -/
def pointedTriangleFamilyEdgeMap (j : Fin 3) :
    pointedPrismFamilyFixedChoice D ⟶
      relativeFunctorSpace pointedSpaceProjection (((stdSimplex.δ j ▷ E) ▷ K) ≫ b₂) :=
  relativeFunctorExtensionSpaceι pointedSpaceProjection b₂
    ((scaffoldFirstVertex 2 ▷ E) ▷ K) D.boundary D.projection ≫
      relativeFunctorPre pointedSpaceProjection b₂ ((stdSimplex.δ j ▷ E) ▷ K)

/-- 制限後の実頂点は、元の全 pointed 延長の同じ全辺そのものを表す。 -/
lemma pointedTriangleFamilyEdgeMap_vertex (j : Fin 3)
    (W : ((Δ[2] : SSet.{u + 1}) ⊗ E) ⊗ K ⟶ PointedSpaceInfinity.{u})
    (hb : ((scaffoldFirstVertex 2 ▷ E) ▷ K) ≫ W = D.boundary)
    (hp : W ≫ pointedSpaceProjection = ((Δ[2] ◁ p) ▷ K) ≫ D.diagram) :
    (((pointedTriangleFamilyEdgeMap D j).app (Opposite.op ⦋0⦌)
      (pointedPrismFamilyFixedChoice_vertex D W hb hp)).val) =
        functorVertex (((stdSimplex.δ j ▷ E) ▷ K) ≫ W) := rfl

end SerrePositivity.InfinityCategories.F2
