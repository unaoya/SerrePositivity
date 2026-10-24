module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.SpaceCompositionZeroLastNativeIdentity
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.RelativePrismSpecifiedNaturality

/-!
概要：零面の最後辺の実終点比較と指定対角比較の合成は、標準族の指定対角比較。
方針：同じ制限比較の自然性正方形から、恒等な native 像を除く。
規約：実終点表示を明示し、元の指定比較と全初点係数を保持する。
使われ方：零面の値と元の二辺評価比較の照合。
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
local notation "β" => r ≫ (fst Δ[2] A ≫ SSet.yonedaEquiv.symm M)
local notation "L" => spaceCompositionTetrahedronZeroFamily s
local notation "W" => r ≫ spaceSimplexPointedFamily M
local notation "W'" => r ≫ L
local notation "a" => coherentNerveVertex
  (EnrichedFunctor.obj s (SimplicialThickening.mk (ULift.up 1)))
local notation "b" => coherentNerveVertex
  (EnrichedFunctor.obj s (SimplicialThickening.mk (ULift.up 2)))
local notation "f" => spaceCompositionZeroMiddleMap s
local notation "e" => spaceCompositionTetrahedronZeroRestrictionIso s r
local notation "h₀" => Eq.trans (Eq.symm (Category.assoc _ _ _))
  (Eq.trans (congrArg (fun t => t ≫ (fst Δ[2] A ≫ SSet.yonedaEquiv.symm M))
    (spaceCompositionZeroLast_start s)) (spaceCompositionZeroMiddle_base s))
local notation "h₁" => Eq.trans (Eq.symm (Category.assoc _ _ _))
  (Eq.trans (congrArg (fun t => t ≫ (fst Δ[2] A ≫ SSet.yonedaEquiv.symm M))
    (spaceCompositionZeroLast_end s)) (spaceCompositionZeroEndpoint_base s))

/-- 同じ零面の最後辺の底は、元の最大化図式の同じ制限。 -/
lemma spaceCompositionZeroLast_standard_projection : W ≫ p = β := by
  rw [Category.assoc, spaceSimplexPointedFamily_projection]
  rfl

/-- 元の零面の最後辺も同じ制限図式を被覆する。 -/
lemma spaceCompositionZeroLast_zero_projection : W' ≫ p = β := by
  rw [Category.assoc, spaceCompositionTetrahedronZeroFamily_projection]

/-- 標準族の実最後辺は、元の中間射から始まる。 -/
lemma spaceCompositionZeroLast_standard_start :
    prismEndpoint 0 A ≫ W = f ≫ vertexFiberι p a := by
  rw [← Category.assoc, spaceCompositionZeroLast_start]
  exact spaceCompositionZeroMiddleMap_standard s

/-- 零面の実最後辺も同じ元の中間射から始まる。 -/
lemma spaceCompositionZeroLast_zero_start :
    prismEndpoint 0 A ≫ W' = f ≫ vertexFiberι p a := by
  rw [← Category.assoc, spaceCompositionZeroLast_start]
  exact spaceCompositionZeroMiddleMap_zero s

/-- 零面の同じ実終点像と指定対角比較の合成は、標準族の指定対角比較そのもの。 -/
lemma spaceCompositionZeroLastSpecified_endpoint_square
    (g g' : A ⟶ vertexFiber p b)
    (hg : prismEndpoint 1 A ≫ W = g ≫ vertexFiberι p b)
    (hg' : prismEndpoint 1 A ≫ W' = g' ≫ vertexFiberι p b) :
    relativePrismActualEndpointIso p β b h₁ W W'
      (spaceCompositionZeroLast_standard_projection s) (spaceCompositionZeroLast_zero_projection s)
      g g' hg hg' e ≪≫
        leftFibrationPrism_diagonalTransportIso p f g' β h₀ h₁ W'
          (spaceCompositionZeroLast_zero_start s) hg'
          (spaceCompositionZeroLast_zero_projection s) =
      leftFibrationPrism_diagonalTransportIso p f g β h₀ h₁ W
        (spaceCompositionZeroLast_standard_start s) hg
        (spaceCompositionZeroLast_standard_projection s) := by
  have h := relativePrismSpecified_naturality p β a b h₀ h₁ W W'
    (spaceCompositionZeroLast_standard_projection s) (spaceCompositionZeroLast_zero_projection s)
    f f g g' (spaceCompositionZeroLast_standard_start s) (spaceCompositionZeroLast_zero_start s)
    hg hg' e
  rw [spaceCompositionZeroLastNativeEndpointIso_eq_refl, Iso.trans_refl] at h
  exact h

end SerrePositivity.InfinityCategories.F2
