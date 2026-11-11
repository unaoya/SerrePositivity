module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.SpaceSimplexPointedFamilyComparison
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.RelativeFunctorExtensionEndpoint
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.VertexIsoEndpointTransport

/-!
概要：同じ全 pointed 比較を、任意の部分図式へ底を保って制限する。
方針：同じ相対延長空間の指定比較を、相対前合成の射で写す。
規約：部分図式ごとに比較を選び直さない。使われ方：三辺と指定 path の同時比較。
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

/-- 任意の部分図式の比較は、元の同じ全比較を底を保つ相対前合成で写した値。 -/
def spaceSimplexPointedFamilyRestrictionIso
    (L : (Δ[n] : SSet.{u + 1}) ⊗ A ⟶ PointedSpaceInfinity.{u})
    (hL : L ≫ pointedSpaceProjection = b) (hL₀ : i ≫ L = v)
    {C : SSet.{u + 1}} (r : C ⟶ (Δ[n] : SSet.{u + 1}) ⊗ A)
 :=
  vertexIsoOfEq
    (VertexIso.map (spaceSimplexPointedFamilyComparisonIso s L hL hL₀)
      (relativeFunctorExtensionSpaceι pointedSpaceProjection b i v
        (spaceSimplexPointedFamily_boundary s) ≫ relativeFunctorPre pointedSpaceProjection b r))
    (relativeFunctorPre_vertex pointedSpaceProjection b r (spaceSimplexPointedFamily s)
      (spaceSimplexPointedFamily_projection s))
    (relativeFunctorPre_vertex pointedSpaceProjection b r L hL)

/-- 両端を実際の制限射に揃えても、同じ全比較の指定像の値そのものを保持する。 -/
lemma spaceSimplexPointedFamilyRestrictionIso_heq
    (L : (Δ[n] : SSet.{u + 1}) ⊗ A ⟶ PointedSpaceInfinity.{u})
    (hL : L ≫ pointedSpaceProjection = b) (hL₀ : i ≫ L = v)
    {C : SSet.{u + 1}} (r : C ⟶ (Δ[n] : SSet.{u + 1}) ⊗ A)
 :
    HEq (spaceSimplexPointedFamilyRestrictionIso s L hL hL₀ r)
      (VertexIso.map (spaceSimplexPointedFamilyComparisonIso s L hL hL₀)
        (relativeFunctorExtensionSpaceι pointedSpaceProjection b i v
          (spaceSimplexPointedFamily_boundary s) ≫
            relativeFunctorPre pointedSpaceProjection b r)) :=
  vertexIsoOfEq_heq _ _ _

end SerrePositivity.InfinityCategories.F2
