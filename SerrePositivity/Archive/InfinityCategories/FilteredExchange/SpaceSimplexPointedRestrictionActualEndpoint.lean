module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.SpaceSimplexPointedRestrictionEndpointImage
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.RelativePrismEndpointComparisons

/-!
概要：全 pointed 比較の辺制限の実終点像を、同じ全終点比較へ厳密に戻す。
方針：汎用の制限端点像の式を、実終点表示の頂点等式で正規化する。
規約：全係数と指定された全比較を保つ。
使われ方：具体的な零面を展開せずに最後辺の実終点像を計算する。
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

/-- 概要：辺制限の実終点像を回収。方針：制限端点公式で正規化。
規約：指定比較を保持。使われ方：零面の最後辺の終点照合。 -/
lemma spaceSimplexPointedRestrictionActualEndpointIso_eq_endpoint
    (L : (Δ[n] : SSet.{u + 1}) ⊗ A ⟶ PointedSpaceInfinity.{u})
    (hL : L ≫ p = β) (hL₀ : j ≫ L = v)
    {Q : SSet.{u + 1}} (r : (Δ[1] : SSet.{u + 1}) ⊗ Q ⟶ (Δ[n] : SSet.{u + 1}) ⊗ A)
    (k : Q ⟶ (Δ[n] : SSet.{u + 1}) ⊗ A) (hk : prismEndpoint 1 Q ≫ r = k)
    (z : SpaceInfinity.{u} _⦋0⦌) (hz : k ≫ β = SSet.const z)
    (g g' : Q ⟶ vertexFiber p z)
    (hg : k ≫ spaceSimplexPointedFamily s = g ≫ vertexFiberι p z)
    (hg' : k ≫ L = g' ≫ vertexFiberι p z) :
    relativePrismActualEndpointIso p (r ≫ β) z
      ((Category.assoc _ _ _).symm.trans ((congrArg (fun t => t ≫ β) hk).trans hz))
      (r ≫ spaceSimplexPointedFamily s) (r ≫ L)
      (by rw [Category.assoc, spaceSimplexPointedFamily_projection])
      (by rw [Category.assoc, hL]) g g'
      (by rw [← Category.assoc, hk]; exact hg)
      (by rw [← Category.assoc, hk]; exact hg')
      (spaceSimplexPointedFamilyRestrictionIso s L hL hL₀ r) =
        spaceSimplexPointedFamilyEndpointIso s L hL hL₀ k z hz g g' hg hg' := by
  unfold relativePrismActualEndpointIso
  exact eq_of_heq ((vertexIsoOfEq_heq _ _ _).trans
    (spaceSimplexPointedRestrictionEndpointImage_heq_endpoint s L hL hL₀ r 1 k hk z hz
      g g' hg hg'))

end SerrePositivity.InfinityCategories.F2
