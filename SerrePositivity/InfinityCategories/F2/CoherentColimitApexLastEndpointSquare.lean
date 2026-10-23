module

public import SerrePositivity.InfinityCategories.F2.CoherentColimitApexLastInitialEndpoint
public import SerrePositivity.InfinityCategories.F2.CoherentColimitApexLastActualEndpoint
public import SerrePositivity.InfinityCategories.F2.RelativePrismSpecifiedNaturality
public import SerrePositivity.InfinityCategories.F2.RelativePrismInitialEndpoint

/-!
概要：元の最後辺の自然性を、同じ全三角形の実中間・終点比較で書く。
方針：二実 prism・実両端・同じ raw 区間を保持し、全相対関手の自然性を使う。
規約：同じ全初点係数を保持。使われ方：元の二辺評価の因子式の中間・終点照合。
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
local notation "I" => relativePrismInitialEndpointIso p β x h₀ W W' hW hW' f f' hs hs' e
local notation "E" => relativePrismActualEndpointIso p β y h₁ W W' hW hW' g g' he he' e
local notation "N" => relativePrismNativeEndpointIso p β x y h₀ h₁ W W' hW hW' f f' hs hs' e
local notation "D" => leftFibrationPrism_diagonalTransportIso p f g β h₀ h₁ W hs he hW
local notation "D'" => leftFibrationPrism_diagonalTransportIso p f' g' β h₀ h₁ W' hs' he' hW'

/-- 元の全三角形の終点比較で書いた、同じ実最後辺の指定自然性正方形。 -/
lemma coherentColimitApexLastSpecified_endpoint_square :
    coherentColimitApexPointedTargetEndpointIso B T ≪≫ D' = D ≪≫ N := by
  simpa only [coherentColimitApexLastActualEndpointIso_eq_target] using
    coherentColimitApexLastSpecified_naturality B T

/-- 同じ実最後辺の native 像は、元の全三角形の中間比較の同じ輸送による後合成。 -/
lemma coherentColimitApexLastNative_heq_middle_postcomp :
    HEq N (FunctorIso.postcomp (coherentColimitApexPointedMiddleEndpointIso B T)
      ((functorVertexEquiv _ _).symm
        ((parametrizedFiberTransport p x y).app (Opposite.op ⦋0⦌)
          (coherentColimitRawIntervalVertex B b)))) := by
  have h := coherentColimitApexLastNative_heq_initial_postcomp B T
  rw [coherentColimitApexLastInitialEndpointIso_eq_middle] at h
  exact h

end SerrePositivity.InfinityCategories.F2
