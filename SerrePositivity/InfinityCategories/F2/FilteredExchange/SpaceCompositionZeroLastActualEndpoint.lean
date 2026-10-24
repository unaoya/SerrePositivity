module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.SpaceCompositionZeroLastSpecifiedSquare
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.SpaceCompositionZeroTargetMaps
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.SpaceSimplexPointedRestrictionActualEndpoint

/-!
概要：零面の最後辺の指定実終点像は、元の反転精密化の同じ全係数作用。
方針：同じ全比較の辺制限と全終点評価を照合し、両端だけを正規化する。
規約：指定比較の値と元の二辺合成・長辺作用を保持する。
使われ方：最後辺の自然性正方形を零面の指定値で表示する。
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
local notation "j" => simplexPrismVertex 2 2 A
local notation "b" => coherentNerveVertex
  (EnrichedFunctor.obj s (SimplicialThickening.mk (ULift.up 2)))
local notation "g" => spaceCompositionZeroCompositeMap s
local notation "g'" => spaceCompositionZeroTargetMap s
local notation "f" => spaceCompositionZeroMiddleMap s
local notation "h₀" => Eq.trans (Eq.symm (Category.assoc _ _ _))
  (Eq.trans (congrArg (fun t => t ≫ β) (spaceCompositionZeroLast_start s))
    (spaceCompositionZeroMiddle_base s))
local notation "h₁" => Eq.trans (Eq.symm (Category.assoc _ _ _))
  (Eq.trans (congrArg (fun t => t ≫ β) (spaceCompositionZeroLast_end s))
    (spaceCompositionZeroEndpoint_base s))

/-- 概要：標準族の最後辺の終点は同じ元の二辺合成作用。方針：汎用制限端点式で正規化。
規約：指定比較の値を保持。使われ方：零面の最後辺の値照合。 -/
lemma spaceCompositionZeroLast_standard_end :
    prismEndpoint 1 A ≫ (r ≫ spaceSimplexPointedFamily M) = g ≫ vertexFiberι p b := by
  rw [← Category.assoc, spaceCompositionZeroLast_end]
  exact spaceCompositionZeroCompositeMap_standard s

/-- 概要：零面の最後辺の終点は同じ元の長辺作用。方針：汎用制限端点式で正規化。
規約：指定比較の値を保持。使われ方：零面の最後辺の値照合。 -/
lemma spaceCompositionZeroLast_zero_end :
    prismEndpoint 1 A ≫ (r ≫ L) = g' ≫ vertexFiberι p b := by
  rw [← Category.assoc, spaceCompositionZeroLast_end]
  exact spaceCompositionZeroTargetMap_zero s

/-- 概要：同じ最後辺制限比較の実終点像は、元の反転精密化の指定作用そのもの。方針：汎用制限端点式で正規化。
規約：指定比較の値を保持。使われ方：零面の最後辺の値照合。 -/
lemma spaceCompositionZeroLastActualEndpointIso_eq_zero :
    relativePrismActualEndpointIso p (r ≫ β) b h₁
      (r ≫ spaceSimplexPointedFamily M) (r ≫ L)
      (spaceCompositionZeroLast_standard_projection s) (spaceCompositionZeroLast_zero_projection s)
      g g' (spaceCompositionZeroLast_standard_end s) (spaceCompositionZeroLast_zero_end s)
      (spaceCompositionTetrahedronZeroRestrictionIso s r) =
        pointedOppositeTriangleFunctorIso s := by
  have ht := spaceSimplexPointedRestrictionActualEndpointIso_eq_endpoint M L
    (spaceCompositionTetrahedronZeroFamily_projection s)
    (spaceCompositionTetrahedronZeroFamily_initial s) r j (spaceCompositionZeroLast_end s)
    b (spaceCompositionZeroEndpoint_base s) g g'
    (spaceCompositionZeroCompositeMap_standard s) (spaceCompositionZeroTargetMap_zero s)
  exact eq_of_heq ((heq_of_eq ht).trans (spaceCompositionZeroTargetEndpointIso_heq_zero s))

/-- 概要：零面の同じ実最後辺の指定対角比較。方針：実両端と底を固定する。
規約：全初点係数を保持。使われ方：Apex 側の同じ実最後辺との値照合。 -/
def spaceCompositionZeroLastDiagonal :=
  leftFibrationPrism_diagonalTransportIso p f g' (r ≫ β) h₀ h₁ (r ≫ L)
    (spaceCompositionZeroLast_zero_start s) (spaceCompositionZeroLast_zero_end s)
    (spaceCompositionZeroLast_zero_projection s)

/-- 概要：元の零面の値による最後辺の正方形。方針：同じ実終点像を代入。
規約：指定対角比較を保持。使われ方：二辺評価の因子式への代入。 -/
lemma spaceCompositionZeroLastSpecified_zero_square :
    pointedOppositeTriangleFunctorIso s ≪≫ spaceCompositionZeroLastDiagonal s =
      leftFibrationPrism_diagonalTransportIso p f g (r ≫ β) h₀ h₁
        (r ≫ spaceSimplexPointedFamily M)
        (spaceCompositionZeroLast_standard_start s) (spaceCompositionZeroLast_standard_end s)
        (spaceCompositionZeroLast_standard_projection s) := by
  have h := spaceCompositionZeroLastSpecified_endpoint_square s g g'
    (spaceCompositionZeroLast_standard_end s) (spaceCompositionZeroLast_zero_end s)
  rw [spaceCompositionZeroLastActualEndpointIso_eq_zero] at h
  exact h

end SerrePositivity.InfinityCategories.F2
