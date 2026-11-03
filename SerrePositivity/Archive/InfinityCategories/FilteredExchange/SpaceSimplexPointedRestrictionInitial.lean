module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.SpaceSimplexPointedRestrictionNaturality
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.VertexIsoConstantValue

/-!
概要：同じ全 pointed 比較の初点への像は、元の全初点族の恒等同型となる。
方針：延長空間の全初点制限が定値である厳密な式を、同じ比較の像に使う。
規約：元の全係数と指定同型を保持。使われ方：第一辺と長辺の共通始点での整合。
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

/-- 同じ全比較の始点制限は、元の全初点族の相対頂点における恒等同型。 -/
lemma spaceSimplexPointedFamilyRestrictionIso_initial
    (L : (Δ[n] : SSet.{u + 1}) ⊗ A ⟶ PointedSpaceInfinity.{u})
    (hL : L ≫ pointedSpaceProjection = b) (hL₀ : i ≫ L = v) :
    HEq (spaceSimplexPointedFamilyRestrictionIso s L hL hL₀ i)
      (Iso.refl (SSet.HomotopyCategory.mk
        (relativeFunctorVertex pointedSpaceProjection (i ≫ b) v
          (spaceSimplexPointedFamily_boundary s)))) := by
  have : KanComplex (spaceSimplexPointedFamilyExtensionSpace s) :=
    (spaceSimplexPointedFamilyExtensionSpace_contractible s).kanComplex
  exact (spaceSimplexPointedFamilyRestrictionIso_heq s L hL hL₀ i).trans
    (vertexIso_map_heq_refl_of_eq_const (spaceSimplexPointedFamilyComparisonIso s L hL hL₀)
      _ (relativeFunctorExtensionSpaceι_pre pointedSpaceProjection b i v
        (spaceSimplexPointedFamily_boundary s)))

end SerrePositivity.InfinityCategories.F2
