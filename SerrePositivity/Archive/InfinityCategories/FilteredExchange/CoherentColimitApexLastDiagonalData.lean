module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitApexLastEndpointSquare

/-!
概要：元の実最後辺の同じ指定対角比較と native 像を、値の因子式で使える名前で保持する。
方針：元の正方形と同じ実 prism・実両端・指定比較をそのまま公開する。
規約：指定比較や輸送を再選択しない。
使われ方：Ncomp の元の raw 最後辺値と中間比較の因子式。
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
local notation "q" => coherentColimitApexCoefficientMap B T
local notation "x" => JoinCocone.vertex (coherentDiagramTotalCocone G)
local notation "y" => JoinCocone.vertex (coherentDiagramTotalCocone J)
local notation "v" => (SSet.const (coherentColimitRawIntervalVertex B b) : A ⟶ _)
local notation "β" => intervalMappingUncurry v
local notation "h₀" => intervalMappingUncurry_zero v
local notation "h₁" => intervalMappingUncurry_one v
local notation "W" => coherentColimitApexPointedLastPrism B T
local notation "f" => coherentColimitApexMiddleCoefficientMap B T
local notation "f'" => q ≫ coherentColimitRawFiberTransport B a
local notation "g" => coherentColimitApexTargetCoefficientMap B T
local notation "g'" => f' ≫ coherentColimitRawFiberTransport B b
local notation "W'" => coherentColimitRawTransportPointPrism B b f'
local notation "hW" => coherentColimitApexPointedLastPrism_projection_constant B T
local notation "hW'" => coherentColimitRawTransportPointPrism_projection_constant B b f'
local notation "hs" => coherentColimitApexPointedLastPrism_start B T
local notation "hs'" => coherentColimitRawTransportPointPrism_start B b f'
local notation "he" => coherentColimitApexPointedLastPrism_finish B T
local notation "he'" => coherentColimitRawTransportPointPrism_finish B b f'
local notation "e" => coherentColimitApexPointedLastConstantIso B T
local notation "N" => relativePrismNativeEndpointIso p β x y h₀ h₁ W W' hW hW' f f' hs hs' e
local notation "D" => leftFibrationPrism_diagonalTransportIso p f g β h₀ h₁ W hs he hW


/-- 概要：元の実最後辺の指定対角比較。方針：同じ元のデータを保持する。
規約：指定値を保持。使われ方：最後辺の値の因子式。 -/
abbrev coherentColimitApexLastDiagonalComparison := D

/-- 概要：元の同じ最後辺比較の native 像。方針：同じ実相対比較を保持する。
規約：全初期値を保持。使われ方：同じ中間比較の普遍輸送による後合成との照合。 -/
abbrev coherentColimitApexLastNativeImageIso := N

end SerrePositivity.InfinityCategories.F2
