module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.SpaceCompositionZeroMiddleIdentity
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.SpaceSimplexPointedRestrictionEndpointImage
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.RelativePrismNativeInitialIdentity

/-!
概要：零面の最後辺の指定始点像を、元の中間点比較へ戻す。
方針：同じ全比較の制限端点像を計算し、実頂点等式で正規化する。
規約：元の全初点係数と指定比較を保持する。
使われ方：始点像の恒等性を最後辺の native 終点像へ送る。
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
variable (s : SpaceInfinity.{u} _⦋2⦌)
local notation "p" => pointedSpaceProjection
local notation "A" => spaceSimplexPointedCoefficients s
local notation "M" => coherentSimplexMaximalization s
local notation "r" => stdSimplex.δ (0 : Fin 3) ▷ A
local notation "β" => fst Δ[2] A ≫ SSet.yonedaEquiv.symm M
local notation "L" => spaceCompositionTetrahedronZeroFamily s
local notation "W" => r ≫ spaceSimplexPointedFamily M
local notation "W'" => r ≫ L
local notation "a" => coherentNerveVertex
  (EnrichedFunctor.obj s (SimplicialThickening.mk (ULift.up 1)))
local notation "g" => spaceCompositionZeroMiddleMap s
local notation "e" => spaceCompositionTetrahedronZeroRestrictionIso s r

/-- 概要：元の最後辺の始点包含は同じ全三角形の中間頂点包含。方針：実包含と指定端点評価を照合。
規約：元の全初点係数を保持。使われ方：最後辺の始点同定。 -/
lemma spaceCompositionZeroLast_start :
    prismEndpoint 0 A ≫ r = simplexPrismVertex 2 1 A := by
  apply SSet.hom_ext
  intro n
  rfl

/-- 概要：元の零面の同じ最後辺制限比較の始点像は、指定中間点比較そのもの。方針：実包含と指定端点評価を照合。
規約：元の全初点係数を保持。使われ方：最後辺の始点同定。 -/
lemma spaceCompositionZeroLastInitialEndpointIso_eq_middle :
    relativePrismInitialEndpointIso p (r ≫ β) a
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun t => t ≫ β) (spaceCompositionZeroLast_start s)).trans
          (spaceCompositionZeroMiddle_base s)))
      W W'
      (by rw [Category.assoc, spaceSimplexPointedFamily_projection]; rfl)
      (by rw [Category.assoc, spaceCompositionTetrahedronZeroFamily_projection]; rfl)
      g g
      (by rw [← Category.assoc, spaceCompositionZeroLast_start]
          exact spaceCompositionZeroMiddleMap_standard s)
      (by rw [← Category.assoc, spaceCompositionZeroLast_start]
          exact spaceCompositionZeroMiddleMap_zero s) e =
        spaceCompositionZeroMiddleEndpointIso s := by
  have ht := spaceSimplexPointedRestrictionEndpointImage_heq_endpoint M L
    (spaceCompositionTetrahedronZeroFamily_projection s)
    (spaceCompositionTetrahedronZeroFamily_initial s) r 0 (simplexPrismVertex 2 1 A)
    (spaceCompositionZeroLast_start s) a (spaceCompositionZeroMiddle_base s) g g
    (spaceCompositionZeroMiddleMap_standard s) (spaceCompositionZeroMiddleMap_zero s)
  unfold relativePrismInitialEndpointIso
  exact eq_of_heq ((vertexIsoOfEq_heq _ _ _).trans ht)

end SerrePositivity.InfinityCategories.F2
