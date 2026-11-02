module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.SpaceSimplexPointedFamilyEndpointWitness
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.TriangleLongPrismRestriction
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.RelativeExtensionFiberWitnessRestriction

/-!
概要：同じ全 pointed 三角形の終点比較を、元の長辺延長空間の指定比較へ戻す。
方針：全三角形の witnessIso を、実長辺と同じ実終点へ制限する。
規約：元の全係数と指定比較を保持。使われ方：長辺の輸送比較との同定。
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
local notation "j" => stdSimplex.δ (1 : Fin 3) ▷ A
local notation "k" => simplexPrismVertex 0 0 A
local notation "r" => simplexPrismVertex 2 2 A

/-- 全三角形の終点像と、同じ実長辺の始点固定延長空間の指定比較は厳密に一致する。 -/
lemma spaceTrianglePointedFamilyEndpointIso_eq_long_witnessIso
    (L : (Δ[2] : SSet.{u + 1}) ⊗ A ⟶ PointedSpaceInfinity.{u})
    (hL : L ≫ pointedSpaceProjection = b) (hL₀ : i ≫ L = v)
    (y : SpaceInfinity.{u} _⦋0⦌) (hy : r ≫ b = SSet.const y)
    (g g' : A ⟶ vertexFiber pointedSpaceProjection y)
    (hg : r ≫ spaceSimplexPointedFamily s = g ≫ vertexFiberι pointedSpaceProjection y)
    (hg' : r ≫ L = g' ≫ vertexFiberι pointedSpaceProjection y) :
    spaceSimplexPointedFamilyEndpointIso s L hL hL₀ r y hy g g' hg hg' =
      relativeExtensionFiberEndpoint_witnessIso pointedSpaceProjection (j ≫ b)
        (prismEndpoint 0 A) (prismEndpoint_zero_leftAnodyne A) (k ≫ v)
        (triangleLongPrism_initial pointedSpaceProjection b v
          (spaceSimplexPointedFamily_boundary s))
        (prismEndpoint 1 A) y (by
          change (prismEndpoint 1 A ≫ j) ≫ b = _
          exact hy)
        (j ≫ spaceSimplexPointedFamily s) (j ≫ L)
        (by rw [Category.assoc, spaceSimplexPointedFamily_projection])
        (by rw [Category.assoc, hL])
        (by rw [← Category.assoc, triangleLongPrism_initial_square, Category.assoc,
          spaceSimplexPointedFamily_firstVertex])
        (by rw [← Category.assoc, triangleLongPrism_initial_square, Category.assoc, hL₀])
        g g' (by change r ≫ spaceSimplexPointedFamily s = _; exact hg)
        (by change r ≫ L = _; exact hg') := by
  rw [spaceSimplexPointedFamilyEndpointIso_eq_witnessIso]
  exact relativeExtensionFiberEndpoint_witnessIso_restriction pointedSpaceProjection b i
    (leftAnodyneExtensions_whiskerRight _ (scaffoldFirstVertex_leftAnodyne 2) A)
    v (spaceSimplexPointedFamily_boundary s) j k (prismEndpoint 0 A)
    (prismEndpoint_zero_leftAnodyne A) (triangleLongPrism_initial_square A)
    r (prismEndpoint 1 A) rfl y hy (spaceSimplexPointedFamily s) L
    (spaceSimplexPointedFamily_projection s) hL
    (spaceSimplexPointedFamily_firstVertex s) hL₀ g g' hg hg'

end SerrePositivity.InfinityCategories.F2
