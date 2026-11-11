module

public import
SerrePositivity.Archive.InfinityCategories.FilteredExchange.SpaceCompositionZeroLastActualEndpoint
public import
SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitApexLastEndpointSquare
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.DiagonalPrismBoundaryValue
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.PointedFiberValueToDisplay
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.DiagonalNativeValueBoundary
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.FunctorIsoSquareIdentity

/-!
概要：零面の実最後辺の指定対角比較の値を、元の Apex の同じ最後辺へ戻す。
方針：共有する実 prism と明示した実両端の等式を、汎用の境界比較へ渡す。
規約：元の全初点係数・実最後辺・値射を保持する。
使われ方：零面の正方形を元の raw 二辺評価比較へ接続する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable (B : SSet.{u})
  {F G J : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}}
  {a : SSet.Homotopy F G} {b : SSet.Homotopy G J} {d : SSet.Homotopy F J}
  (T : FunctorCompositionTriangle a b d)
local notation "p" => pointedSpaceProjection
local notation "s" => coherentColimitApexTriangle B T
local notation "A" => spaceSimplexPointedCoefficients s
local notation "K₂" => EnrichedFunctor.obj s (SimplicialThickening.mk (ULift.up 2))
local notation "β" => intervalMappingUncurry
  (SSet.const (coherentColimitRawIntervalVertex B b) : A ⟶ _)
local notation "W" => coherentColimitApexPointedLastPrism B T
local notation "f" => coherentColimitApexMiddleCoefficientMap B T
local notation "g" => coherentColimitApexTargetCoefficientMap B T
local notation "V₂" => pointedFiberValueTo (coherentColimitApex_raw_two_vertex B T)
local notation "Vcoh" => pointedFiberValueTo (Eq.symm (spaceInfinityVertex_eq_coherent K₂))

/-- 概要：零面と元の Apex の同じ最後辺の値を照合。方針：実境界比較を適用。
規約：元の値射を保持。使われ方：零面の値を raw 二辺比較へ代入する。 -/
lemma coherentColimitApexZeroLastDiagonal_post_value_heq_original :
    HEq ((spaceCompositionZeroLastDiagonal s).postcomp Vcoh)
      ((leftFibrationPrism_diagonalTransportIso p f g β
        (intervalMappingUncurry_zero _) (intervalMappingUncurry_one _) W
        (coherentColimitApexPointedLastPrism_start B T)
        (coherentColimitApexPointedLastPrism_finish B T)
        (coherentColimitApexPointedLastPrism_projection_constant B T)).postcomp V₂) := by
  unfold spaceCompositionZeroLastDiagonal
  apply diagonalTransportIso_postcomp_heq_of_boundary
  · exact (coherentColimitApexMiddleCoefficient_vertex B T).symm
  · exact (coherentColimitApexTargetCoefficient_vertex B T).symm
  · exact spaceCompositionZeroFamily_last_eq_original s
  · exact (pointedFiberValueTo_heq_value (spaceInfinityVertex_eq_coherent K₂).symm).trans
      (pointedFiberValueTo_heq_value (coherentColimitApex_raw_two_vertex B T)).symm

/-- 概要：同じ零面と元の Apex の native 輸送の値射は等しい。
方針：同じ実 prism の底と初期値から値射を照合する。
規約：指定比較の HEq から端点を抽出しない。使われ方：元の中間終点の値照合。 -/
lemma coherentColimitApexZeroLastNative_value_eq_original :
    FunctorIso.targetMap (spaceCompositionZeroLastDiagonal s) ≫ Vcoh =
      diagonalFiberTransport p f (intervalMappingCurryOfEndpoints β
        (intervalMappingUncurry_zero _) (intervalMappingUncurry_one _)) ≫ V₂ := by
  dsimp only [spaceCompositionZeroLastDiagonal, FunctorIso.targetMap]
  apply diagonalFiberTransport_value_eq_of_prism_boundary
    (H := (stdSimplex.δ (0 : Fin 3) ▷ A) ≫ spaceCompositionTetrahedronZeroFamily s)
    (H' := W) (hs := spaceCompositionZeroLast_zero_start s)
    (hs' := coherentColimitApexPointedLastPrism_start B T)
    (hp := spaceCompositionZeroLast_zero_projection s)
    (hp' := coherentColimitApexPointedLastPrism_projection_constant B T)
  · exact (coherentColimitApexMiddleCoefficient_vertex B T).symm
  · exact (coherentColimitApexTargetCoefficient_vertex B T).symm
  · exact spaceCompositionZeroFamily_last_eq_original s
  · exact (pointedFiberValueTo_heq_value (spaceInfinityVertex_eq_coherent K₂).symm).trans
      (pointedFiberValueTo_heq_value (coherentColimitApex_raw_two_vertex B T)).symm
end SerrePositivity.InfinityCategories.F2
