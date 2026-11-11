module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitApexLongNativeDiagonal
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.DiagonalTransportConstantInterval
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitApexRawEdgeValues
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.FunctorIsoTransportAlgebra

/-!
概要：元の長辺直接比較の値を、同じ全初期値・実長辺の指定対角比較の値へ戻す。
方針：一般の一点実 prism の比較式と、元の長辺証人の実一点 prism の厳密な一致を使う。
規約：元の指定比較・全係数を保持。使われ方：元の native 固定射値比較との照合。
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
local notation "A" => spaceSimplexPointedCoefficients (coherentColimitApexTriangle B T)
local notation "q" => coherentColimitApexCoefficientMap B T
local notation "g" => coherentColimitApexTargetCoefficientMap B T
local notation "D" => SSet.yonedaEquiv.symm (coherentColimitRawIntervalVertex B d)
local notation "l" => stdSimplex.obj₀Equiv.symm (0 : Fin 1)
local notation "r" => lift (𝟙 A) (SSet.const l)
local notation "v" => (SSet.const (NatTrans.app D (Opposite.op ⦋0⦌) l) :
  A ⟶ intervalMappingSpace (JoinCocone.vertex (coherentDiagramTotalCocone F))
    (JoinCocone.vertex (coherentDiagramTotalCocone J)))
local notation "β" => intervalMappingUncurry v
local notation "h₀" => intervalMappingUncurry_zero v
local notation "h₁" => intervalMappingUncurry_one v
local notation "P" => coherentColimitApexPointedLongPrism B T
local notation "W" => coherentColimitApexPointedLongTransport B T

local notation "V₂" => pointedFiberValueTo (coherentColimitApex_raw_two_vertex B T)

/-- 元の長辺直接比較の値は、同じ元の全実長辺の指定対角比較の値と一致する。 -/
lemma coherentColimitApexPointedLongNativeComparison_post_value_heq_diagonal :
    HEq ((coherentColimitApexPointedLongNativeComparison B T).postcomp V₂)
      ((leftFibrationPrism_diagonalTransportIso p q g β h₀ h₁ P
        (coherentColimitApexPointedLongPrism_start B T)
        (coherentColimitApexPointedLongPrism_finish B T)
        ((coherentColimitApexPointedLongPrism_projection B T).trans
          (intervalMappingPoint_uncurry D l))).postcomp V₂) := by
  let e := leftFibrationPrism_diagonalTransportIso p q g β h₀ h₁ P
    (coherentColimitApexPointedLongPrism_start B T)
    (coherentColimitApexPointedLongPrism_finish B T)
    ((coherentColimitApexPointedLongPrism_projection B T).trans
      (intervalMappingPoint_uncurry D l))
  have hc : intervalMappingCurryOfEndpoints β h₀ h₁ = v := by
    apply intervalMappingUncurry_injective
    exact intervalMappingUncurry_curryOfEndpoints β h₀ h₁
  have ht : diagonalFiberTransport p q (intervalMappingCurryOfEndpoints β h₀ h₁) =
      q ≫ (functorVertexEquiv _ _).symm
        ((parametrizedFiberTransport p _ _).app (Opposite.op ⦋0⦌)
          (NatTrans.app D (Opposite.op ⦋0⦌) l)) := by
    rw [hc, diagonalFiberTransport_constant_interval]
  exact functorIso_postcomp_heq_of_heq e (coherentColimitApexPointedLongNativeComparison B T)
    rfl ht (coherentColimitApexPointedLongNativeComparison_heq_diagonal B T) V₂

end SerrePositivity.InfinityCategories.F2
