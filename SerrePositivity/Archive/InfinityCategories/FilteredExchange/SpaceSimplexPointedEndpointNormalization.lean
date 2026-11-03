module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.SpaceSimplexPointedFamilyEndpoint

/-!
概要：指定された全終点比較の値を、明示した実両端の表示へ移す。
方針：全終点評価と実端点正規化の整合を、一般の単体の段階で合成する。
規約：比較先の型を独立に量化し、巨大な具体的全族を展開しない。
使われ方：零面の正規化した終点比較の回収。
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
local notation "p" => pointedSpaceProjection
local notation "A" => spaceSimplexPointedCoefficients s
local notation "β" => fst Δ[n] A ≫ SSet.yonedaEquiv.symm s
local notation "i" => scaffoldFirstVertex n ▷ A
local notation "w" => snd Δ[0] A ≫
  pointedCoherentFiberComparison (EnrichedFunctor.obj s (SimplicialThickening.mk (ULift.up 0))) ≫
    vertexFiberι p
      (coherentNerveVertex (EnrichedFunctor.obj s (SimplicialThickening.mk (ULift.up 0))))

/-- 概要：全終点像の同じ値を実両端の表示へ移す。方針：汎用端点比較で合成。
規約：比較先の型を独立に保つ。使われ方：具体的零面の展開を避ける。 -/
lemma spaceSimplexPointedFamilyEndpointIso_heq_of_comparison_heq
    (L : (Δ[n] : SSet.{u + 1}) ⊗ A ⟶ PointedSpaceInfinity.{u})
    (hL : L ≫ p = β) (hL₀ : i ≫ L = w)
    {Q : SSet.{u + 1}} (r : Q ⟶ (Δ[n] : SSet.{u + 1}) ⊗ A)
    (z : SpaceInfinity.{u} _⦋0⦌) (hz : r ≫ β = SSet.const z)
    (g g' : Q ⟶ vertexFiber p z)
    (hg : r ≫ spaceSimplexPointedFamily s = g ≫ vertexFiberι p z)
    (hg' : r ≫ L = g' ≫ vertexFiberι p z) {α : Type (u + 1)} (e : α)
    (he : HEq (VertexIso.map (spaceSimplexPointedFamilyComparisonIso s L hL hL₀)
      (relativeExtensionFiberEndpoint p β i w (spaceSimplexPointedFamily_boundary s) r z hz)) e) :
    HEq (spaceSimplexPointedFamilyEndpointIso s L hL hL₀ r z hz g g' hg hg') e :=
  (spaceSimplexPointedFamilyEndpointIso_heq_map s L hL hL₀ r z hz g g' hg hg').trans he

end SerrePositivity.InfinityCategories.F2
