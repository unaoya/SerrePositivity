module

public import
  SerrePositivity.Archive.InfinityCategories.FilteredExchange.SpaceSimplexPointedFamilyEndpoint
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.RelativeExtensionFiberBoundary
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.VertexIsoConstantValue
/-!
概要：固定初点内の評価による同じ全 pointed 比較の像は元の恒等比較となる。
方針：評価射の定値性を元の指定比較へ写し、実両端の表示を揃える。
規約：全係数・実初点・指定された同じ比較を保持する。
使われ方：第一面の同じ指定比較の実初点像の恒等性。
-/

@[expose] public section
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
open HomotopyLimits
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
variable {n : ℕ} (s : SpaceInfinity.{u} _⦋n⦌)
local notation "A" => spaceSimplexPointedCoefficients s
local notation "b" => fst Δ[n] A ≫ SSet.yonedaEquiv.symm s
local notation "i" => scaffoldFirstVertex n ▷ A
local notation "v" => snd Δ[0] A ≫
  pointedCoherentFiberComparison (EnrichedFunctor.obj s (SimplicialThickening.mk (ULift.up 0))) ≫
    vertexFiberι pointedSpaceProjection
      (coherentNerveVertex (EnrichedFunctor.obj s (SimplicialThickening.mk (ULift.up 0))))
/-- 概要：固定境界に含まれる実初点での指定比較は元の恒等比較。
方針：同じ実初点評価の定値性を使う。
規約：全係数と指定値を保持。使われ方：第一面の初点整合。 -/
lemma spaceSimplexPointedFamilyEndpointIso_eq_refl_of_boundary
    (L : (Δ[n] : SSet.{u + 1}) ⊗ A ⟶ PointedSpaceInfinity.{u})
    (hL : L ≫ pointedSpaceProjection = b) (hL₀ : i ≫ L = v)
    {Q : SSet.{u + 1}} (r : Q ⟶ (Δ[n] : SSet.{u + 1}) ⊗ A)
    (t : Q ⟶ (Δ[0] : SSet.{u + 1}) ⊗ A) (hr : r = t ≫ i)
    (y : SpaceInfinity.{u} _⦋0⦌) (hy : r ≫ b = SSet.const y)
    (g : Q ⟶ vertexFiber pointedSpaceProjection y)
    (hg : r ≫ spaceSimplexPointedFamily s = g ≫ vertexFiberι pointedSpaceProjection y)
    (hg' : r ≫ L = g ≫ vertexFiberι pointedSpaceProjection y)
    (ht : t ≫ v = g ≫ vertexFiberι pointedSpaceProjection y) :
    spaceSimplexPointedFamilyEndpointIso s L hL hL₀ r y hy g g hg hg' =
      Iso.refl (SSet.HomotopyCategory.mk (functorVertex g)) := by
  subst r
  have : KanComplex (spaceSimplexPointedFamilyExtensionSpace s) :=
    (spaceSimplexPointedFamilyExtensionSpace_contractible s).kanComplex
  exact eq_of_heq ((spaceSimplexPointedFamilyEndpointIso_heq_map s L hL hL₀
    (t ≫ i) y hy g g hg hg').trans
      (vertexIso_map_heq_refl_of_eq_const (spaceSimplexPointedFamilyComparisonIso s L hL hL₀)
        (functorVertex g) (relativeExtensionFiberEndpoint_eq_const_of_boundary
          pointedSpaceProjection b i v (spaceSimplexPointedFamily_boundary s) t y hy g ht)))
end
end SerrePositivity.InfinityCategories.F2
