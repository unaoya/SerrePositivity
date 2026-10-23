module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.SpaceSimplexPointedRestrictionNaturality

/-!
概要：同じ全 pointed 比較を二つの経路で制限した値を、元の実制限の一致で同定する。
方針：抽象的な制限射上で自然性と等式の移送を合成する。
規約：具体的な面や頂点の計算と、指定同型の合成の計算を独立に検証する。
使われ方：三辺の共有頂点で同じ全比較を回収する。
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

/-- 実制限の合成が同じなら、同じ全比較の二段の像も指定値まで一致する。 -/
lemma spaceSimplexPointedFamilyRestrictionIso_shared
    (L : (Δ[n] : SSet.{u + 1}) ⊗ A ⟶ PointedSpaceInfinity.{u})
    (hL : L ≫ pointedSpaceProjection = b) (hL₀ : i ≫ L = v)
    {C D Q : SSet.{u + 1}} (r : C ⟶ (Δ[n] : SSet.{u + 1}) ⊗ A)
    (r' : D ⟶ (Δ[n] : SSet.{u + 1}) ⊗ A) (t : Q ⟶ C) (t' : Q ⟶ D)
    (h : t ≫ r = t' ≫ r') :
    HEq (VertexIso.map (spaceSimplexPointedFamilyRestrictionIso s L hL hL₀ r)
        (relativeFunctorPre pointedSpaceProjection (r ≫ b) t))
      (VertexIso.map (spaceSimplexPointedFamilyRestrictionIso s L hL hL₀ r')
        (relativeFunctorPre pointedSpaceProjection (r' ≫ b) t')) :=
  (spaceSimplexPointedFamilyRestrictionIso_precomp s L hL hL₀ r t).trans
    ((spaceSimplexPointedFamilyRestrictionIso_congr s L hL hL₀ h).trans
      (spaceSimplexPointedFamilyRestrictionIso_precomp s L hL hL₀ r' t').symm)

end SerrePositivity.InfinityCategories.F2
