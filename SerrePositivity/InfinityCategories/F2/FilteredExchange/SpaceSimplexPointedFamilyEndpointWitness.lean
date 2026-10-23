module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.SpaceSimplexPointedFamilyEndpoint
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.RelativeExtensionFiberEndpointValue

/-!
概要：元の全 pointed 比較の終点像を、同じ実二延長の witnessIso と厳密に同定する。
方針：両方を同じ可縮な延長空間の指定同型の像へ戻す。
規約：元の全単体と全係数を保持。使われ方：同じ長辺延長空間への制限。
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
variable {n : ℕ} (s : SpaceInfinity.{u} _⦋n⦌)
local notation "A" => spaceSimplexPointedCoefficients s
local notation "b" => fst Δ[n] A ≫ SSet.yonedaEquiv.symm s
local notation "i" => scaffoldFirstVertex n ▷ A
local notation "v" => snd Δ[0] A ≫
  pointedCoherentFiberComparison (EnrichedFunctor.obj s (SimplicialThickening.mk (ULift.up 0))) ≫
    vertexFiberι pointedSpaceProjection
      (coherentNerveVertex (EnrichedFunctor.obj s (SimplicialThickening.mk (ULift.up 0))))

/-- 同じ全比較の終点像は、同じ二つの実延長の指定 witnessIso に厳密に一致する。 -/
lemma spaceSimplexPointedFamilyEndpointIso_eq_witnessIso
    (L : (Δ[n] : SSet.{u + 1}) ⊗ A ⟶ PointedSpaceInfinity.{u})
    (hL : L ≫ pointedSpaceProjection = b) (hL₀ : i ≫ L = v)
    {Q : SSet.{u + 1}} (r : Q ⟶ (Δ[n] : SSet.{u + 1}) ⊗ A)
    (y : SpaceInfinity.{u} _⦋0⦌) (hy : r ≫ b = SSet.const y)
    (g g' : Q ⟶ vertexFiber pointedSpaceProjection y)
    (hg : r ≫ spaceSimplexPointedFamily s = g ≫ vertexFiberι pointedSpaceProjection y)
    (hg' : r ≫ L = g' ≫ vertexFiberι pointedSpaceProjection y) :
    spaceSimplexPointedFamilyEndpointIso s L hL hL₀ r y hy g g' hg hg' =
      relativeExtensionFiberEndpoint_witnessIso pointedSpaceProjection b i
        (leftAnodyneExtensions_whiskerRight _ (scaffoldFirstVertex_leftAnodyne n) A)
        v (spaceSimplexPointedFamily_boundary s) r y hy
        (spaceSimplexPointedFamily s) L (spaceSimplexPointedFamily_projection s) hL
        (spaceSimplexPointedFamily_firstVertex s) hL₀ g g' hg hg' := by
  have h₀ := spaceSimplexPointedFamilyEndpointIso_heq_map s L hL hL₀ r y hy g g' hg hg'
  have h₁ := relativeExtensionFiberEndpoint_witnessIso_heq_map pointedSpaceProjection b i
    (leftAnodyneExtensions_whiskerRight _ (scaffoldFirstVertex_leftAnodyne n) A)
    v (spaceSimplexPointedFamily_boundary s) r y hy
    (spaceSimplexPointedFamily s) L (spaceSimplexPointedFamily_projection s) hL
    (spaceSimplexPointedFamily_firstVertex s) hL₀ g g' hg hg'
  exact eq_of_heq (h₀.trans h₁.symm)

end SerrePositivity.InfinityCategories.F2
