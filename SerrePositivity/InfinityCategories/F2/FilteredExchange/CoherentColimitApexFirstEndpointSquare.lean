module

public import
SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentColimitApexFirstInitialEndpoint
public import
SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentColimitApexFirstActualEndpoint
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentColimitRawPointDiagonal
public import
SerrePositivity.InfinityCategories.F2.FilteredExchange.RelativePrismNativeInitialIdentity
public import
SerrePositivity.InfinityCategories.F2.FilteredExchange.RelativePrismSpecifiedNaturality
/-!
概要：元の第一面の同じ指定正方形を、元の中間比較と二つの指定対角比較で保持する。
方針：同じ初点像と native 像を恒等として消去し、実終点像を同じ中間比較へ戻す。
規約：実両端・全係数・元の指定値を保持する。
使われ方：中間比較と raw 第一辺値の貼り合わせ。
-/

@[expose] public section
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
variable (B : SSet.{u})
  {F G J : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}}
  {a : SSet.Homotopy F G} {b : SSet.Homotopy G J} {d : SSet.Homotopy F J}
  (T : FunctorCompositionTriangle a b d)
local notation "p" => pointedSpaceProjection
local notation "s" => coherentColimitApexTriangle B T
local notation "A" => spaceSimplexPointedCoefficients s
local notation "q" => coherentColimitApexCoefficientMap B T
local notation "x" => JoinCocone.vertex (coherentDiagramTotalCocone F)
local notation "y" => JoinCocone.vertex (coherentDiagramTotalCocone G)
local notation "v" => (SSet.const (coherentColimitRawIntervalVertex B a) : A ⟶ _)
local notation "β" => intervalMappingUncurry v
local notation "h₀" => intervalMappingUncurry_zero v
local notation "h₁" => intervalMappingUncurry_one v
local notation "W" => coherentColimitApexPointedFirstPrism B T
local notation "f" => q
local notation "f'" => q
local notation "g" => coherentColimitApexMiddleCoefficientMap B T
local notation "g'" => q ≫ coherentColimitRawFiberTransport B a
local notation "W'" => coherentColimitRawTransportPointPrism B a q
local notation "hW" => coherentColimitApexPointedFirstPrism_projection_constant B T
local notation "hW'" => coherentColimitRawTransportPointPrism_projection_constant B a q
local notation "hs" => coherentColimitApexPointedFirstPrism_start B T
local notation "hs'" => coherentColimitRawTransportPointPrism_start B a q
local notation "he" => coherentColimitApexPointedFirstPrism_finish B T
local notation "he'" => coherentColimitRawTransportPointPrism_finish B a q
local notation "e" => coherentColimitApexPointedFirstConstantIso B T
local notation "I" => relativePrismInitialEndpointIso p β x h₀ W W' hW hW' f f' hs hs' e
local notation "E" => relativePrismActualEndpointIso p β y h₁ W W' hW hW' g g' he he' e
local notation "N" => relativePrismNativeEndpointIso p β x y h₀ h₁ W W' hW hW' f f' hs hs' e
local notation "D" => leftFibrationPrism_diagonalTransportIso p f g β h₀ h₁ W hs he hW
local notation "D'" => leftFibrationPrism_diagonalTransportIso p f' g' β h₀ h₁ W' hs' he' hW'

/-- 概要：元の第一面の同じ指定対角比較。方針：同じ実 prism と両端を保持。
規約：指定値を再選択しない。使われ方：元の第一辺値の回収。 -/
abbrev coherentColimitApexFirstDiagonalComparison := D
/-- 概要：固定初点の同じ第一面比較の native 像は恒等。
方針：元の初点像の恒等性から同じ全区間作用へ移す。
規約：元の比較を保持。使われ方：第一辺の指定正方形の消去。 -/
lemma coherentColimitApexFirstNativeEndpointIso_eq_refl : N = Iso.refl _ := by
  exact relativePrismNativeEndpointIso_eq_refl_of_initial p β x y h₀ h₁
    W W' hW hW' q hs hs' e (coherentColimitApexFirstInitialEndpointIso_eq_refl B T)
/-- 概要：元の中間比較に raw 指定対角比較を続けると元の第一指定対角比較。
方針：同じ自然性正方形の native 恒等因子を消去する。
規約：全係数と実両端を保持。使われ方：第一辺値との貼り合わせ。 -/
lemma coherentColimitApexFirstSpecified_initial_square :
    coherentColimitApexPointedMiddleEndpointIso B T ≪≫
      coherentColimitRawPointDiagonalComparison B a q =
        coherentColimitApexFirstDiagonalComparison B T := by
  have h := relativePrismSpecified_naturality p β x y h₀ h₁ W W' hW hW'
    f f' g g' hs hs' he he' e
  rw [coherentColimitApexFirstActualEndpointIso_eq_middle,
    coherentColimitApexFirstNativeEndpointIso_eq_refl, Iso.trans_refl] at h
  exact h
end
end SerrePositivity.InfinityCategories.F2
