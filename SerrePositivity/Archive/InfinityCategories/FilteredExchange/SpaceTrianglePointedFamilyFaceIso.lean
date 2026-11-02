module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.SpaceTrianglePointedFamilyFaces

/-!
概要：同じ全三角形比較の三面を、元の辺そのものを底とする指定相対同型へ移す。
方針：底の同じ厳密な面等式で、指定された制限同型の表示だけを変える。
規約：第零面と全係数も保持。使われ方：元の三実辺の指定比較の同時照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
open HomotopyLimits
variable (s : SpaceInfinity.{u} _⦋2⦌)
local notation "A" => spaceSimplexPointedCoefficients s
local notation "b" => fst Δ[2] A ≫ SSet.yonedaEquiv.symm s
local notation "i" => scaffoldFirstVertex 2 ▷ A
local notation "v" => snd Δ[0] A ≫
  pointedCoherentFiberComparison (EnrichedFunctor.obj s (SimplicialThickening.mk (ULift.up 0))) ≫
    vertexFiberι pointedSpaceProjection
      (coherentNerveVertex (EnrichedFunctor.obj s (SimplicialThickening.mk (ULift.up 0))))

/-- 同じ全比較の任意の面を、元の同じ全辺上の相対頂点同型として読む。 -/
def spaceTrianglePointedFamilyFaceIso
    (L : (Δ[2] : SSet.{u + 1}) ⊗ A ⟶ PointedSpaceInfinity.{u})
    (hL : L ≫ pointedSpaceProjection = b) (hL₀ : i ≫ L = v) (j : Fin 3) :=
  relativeVertexIsoOfEq pointedSpaceProjection
    (spaceSimplexPointedFamilyRestrictionIso s L hL hL₀ (stdSimplex.δ j ▷ A))
    (spaceTrianglePointedFace_base s A j) rfl rfl
    (spaceTrianglePointedFace_projection s (spaceSimplexPointedFamily s)
      (spaceSimplexPointedFamily_projection s) j)
    (spaceTrianglePointedFace_projection s L hL j)

/-- 底を同じ元の辺に揃えても、元の同じ全比較の面への像の値を保持する。 -/
lemma spaceTrianglePointedFamilyFaceIso_heq
    (L : (Δ[2] : SSet.{u + 1}) ⊗ A ⟶ PointedSpaceInfinity.{u})
    (hL : L ≫ pointedSpaceProjection = b) (hL₀ : i ≫ L = v) (j : Fin 3) :
    HEq (spaceTrianglePointedFamilyFaceIso s L hL hL₀ j)
      (spaceSimplexPointedFamilyRestrictionIso s L hL hL₀ (stdSimplex.δ j ▷ A)) :=
  relativeVertexIsoOfEq_heq _ _ _ _ _ _ _

end SerrePositivity.InfinityCategories.F2
