module

public import SerrePositivity.InfinityCategories.F2.SpaceSimplexPointedFamilyEndpoint
public import SerrePositivity.InfinityCategories.F2.SpaceSimplexPointedRestrictionNaturality
public import SerrePositivity.InfinityCategories.F2.RelativePrismEndpointPrecomposition

/-!
概要：全三角形の同じ制限比較の両端像を、元の全相対延長の同じ端点像へ戻す。
方針：同じ指定比較の二段の像と、全端点評価の相対前合成の式を使う。
規約：指定値を保持。使われ方：最後面の実両端像と全三角形の中間・終点比較の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
open HomotopyLimits
variable {n : ℕ} (s : SpaceInfinity.{u} _⦋n⦌)
local notation "p" => pointedSpaceProjection
local notation "A" => spaceSimplexPointedCoefficients s
local notation "β" => fst Δ[n] A ≫ SSet.yonedaEquiv.symm s
local notation "j" => scaffoldFirstVertex n ▷ A
local notation "v" => snd Δ[0] A ≫
  pointedCoherentFiberComparison (EnrichedFunctor.obj s (SimplicialThickening.mk (ULift.up 0))) ≫
    vertexFiberι p
      (coherentNerveVertex (EnrichedFunctor.obj s (SimplicialThickening.mk (ULift.up 0))))

/-- 同じ全相対延長比較の辺制限の両端像は、元の同じ全端点評価の指定像。 -/
lemma spaceSimplexPointedRestrictionEndpointImage_heq
    (L : (Δ[n] : SSet.{u + 1}) ⊗ A ⟶ PointedSpaceInfinity.{u})
    (hL : L ≫ p = β) (hL₀ : j ≫ L = v)
    {Q : SSet.{u + 1}} (r : (Δ[1] : SSet.{u + 1}) ⊗ Q ⟶ (Δ[n] : SSet.{u + 1}) ⊗ A)
    (i : Fin 2) (z : SpaceInfinity.{u} _⦋0⦌)
    (hz : (prismEndpoint i Q ≫ r) ≫ β = SSet.const z) :
    HEq (VertexIso.map (spaceSimplexPointedFamilyRestrictionIso s L hL hL₀ r)
      (curry (relativePrismEvaluationEndpoint p (r ≫ β) i z
        ((Category.assoc (prismEndpoint i Q) r β).symm.trans hz))))
      (VertexIso.map (spaceSimplexPointedFamilyComparisonIso s L hL hL₀)
        (relativeExtensionFiberEndpoint p β j v (spaceSimplexPointedFamily_boundary s)
          (prismEndpoint i Q ≫ r) z hz)) := by
  have hs := vertexIsoOfEq_map_heq
    (VertexIso.map (spaceSimplexPointedFamilyComparisonIso s L hL hL₀)
      (relativeFunctorExtensionSpaceι p β j v (spaceSimplexPointedFamily_boundary s) ≫
        relativeFunctorPre p β r))
    (relativeFunctorPre_vertex p β r (spaceSimplexPointedFamily s)
      (spaceSimplexPointedFamily_projection s))
    (relativeFunctorPre_vertex p β r L hL)
    (curry (relativePrismEvaluationEndpoint p (r ≫ β) i z
      ((Category.assoc (prismEndpoint i Q) r β).symm.trans hz)))
  rw [vertexIso_map_comp] at hs
  refine hs.trans (vertexIso_map_heq _ ?_)
  unfold relativeExtensionFiberEndpoint
  rw [Category.assoc, relativePrismEvaluationEndpoint_restrict_eq_pre p β r i z hz]

/-- 同じ実端点の部分図式を明示して揃えると、元の全端点比較そのものを回収する。 -/
lemma spaceSimplexPointedRestrictionEndpointImage_heq_endpoint
    (L : (Δ[n] : SSet.{u + 1}) ⊗ A ⟶ PointedSpaceInfinity.{u})
    (hL : L ≫ p = β) (hL₀ : j ≫ L = v)
    {Q : SSet.{u + 1}} (r : (Δ[1] : SSet.{u + 1}) ⊗ Q ⟶ (Δ[n] : SSet.{u + 1}) ⊗ A)
    (i : Fin 2) (k : Q ⟶ (Δ[n] : SSet.{u + 1}) ⊗ A)
    (hk : prismEndpoint i Q ≫ r = k)
    (z : SpaceInfinity.{u} _⦋0⦌) (hz : k ≫ β = SSet.const z)
    (g g' : Q ⟶ vertexFiber p z)
    (hg : k ≫ spaceSimplexPointedFamily s = g ≫ vertexFiberι p z)
    (hg' : k ≫ L = g' ≫ vertexFiberι p z) :
    HEq (VertexIso.map (spaceSimplexPointedFamilyRestrictionIso s L hL hL₀ r)
      (curry (relativePrismEvaluationEndpoint p (r ≫ β) i z
        ((Category.assoc (prismEndpoint i Q) r β).symm.trans
          ((congrArg (fun t => t ≫ β) hk).trans hz)))))
      (spaceSimplexPointedFamilyEndpointIso s L hL hL₀ k z hz g g' hg hg') := by
  cases hk
  exact (spaceSimplexPointedRestrictionEndpointImage_heq s L hL hL₀ r i z hz).trans
    (spaceSimplexPointedFamilyEndpointIso_heq_map s L hL hL₀ _ z hz g g' hg hg').symm

end SerrePositivity.InfinityCategories.F2
