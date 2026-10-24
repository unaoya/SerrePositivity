module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.SpaceCompositionZeroLastInitialEndpoint
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.SpaceCompositionZeroEndpointAction

/-!
概要：零面の最後辺の同じ制限比較の native 終点像は恒等である。
方針：指定始点像を元の中間点比較へ同定し、恒等性を全区間族の作用で送る。
規約：全初点係数・底・実最後辺・指定比較を保つ。
使われ方：零面と標準族の最後辺の指定対角比較を自然性で照合する。
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
local notation "b" => coherentNerveVertex
  (EnrichedFunctor.obj s (SimplicialThickening.mk (ULift.up 2)))
local notation "g" => spaceCompositionZeroMiddleMap s
local notation "e" => spaceCompositionTetrahedronZeroRestrictionIso s r

/-- 概要：元の最後辺の終点包含は同じ全三角形の終頂点包含。方針：指定始点像の恒等性を輸送。
規約：元の制限比較を保持。使われ方：最後辺の自然性の整理。 -/
lemma spaceCompositionZeroLast_end :
    prismEndpoint 1 A ≫ r = simplexPrismVertex 2 2 A := by
  apply SSet.hom_ext
  intro n
  rfl

/-- 概要：零面の最後辺の同じ全相対比較の native 終点像は厳密に恒等。方針：指定始点像の恒等性を輸送。
規約：元の制限比較を保持。使われ方：最後辺の自然性の整理。 -/
lemma spaceCompositionZeroLastNativeEndpointIso_eq_refl :
    relativePrismNativeEndpointIso p (r ≫ β) a b
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun t => t ≫ β) (spaceCompositionZeroLast_start s)).trans
          (spaceCompositionZeroMiddle_base s)))
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun t => t ≫ β) (spaceCompositionZeroLast_end s)).trans
          (spaceCompositionZeroEndpoint_base s)))
      W W'
      (by rw [Category.assoc, spaceSimplexPointedFamily_projection]; rfl)
      (by rw [Category.assoc, spaceCompositionTetrahedronZeroFamily_projection]; rfl)
      g g
      (by rw [← Category.assoc, spaceCompositionZeroLast_start]
          exact spaceCompositionZeroMiddleMap_standard s)
      (by rw [← Category.assoc, spaceCompositionZeroLast_start]
          exact spaceCompositionZeroMiddleMap_zero s) e = Iso.refl _ := by
  apply relativePrismNativeEndpointIso_eq_refl_of_initial
  rw [spaceCompositionZeroLastInitialEndpointIso_eq_middle,
    spaceCompositionZeroMiddleEndpointIso_eq_refl]

end SerrePositivity.InfinityCategories.F2
