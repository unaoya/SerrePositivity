module

public import SerrePositivity.InfinityCategories.F2.CoherentColimitApexPointedLongNativeComposition
public import SerrePositivity.InfinityCategories.F2.TransportPointDiagonalComparison
public import SerrePositivity.InfinityCategories.F2.DiagonalPrismComparisonEquality

/-!
概要：元の長辺直接比較を、同じ全初期値・実長辺の元の対角普遍比較へ戻す。
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

/-- 元の長辺直接比較は、同じ元の全実長辺と全初期値の対角普遍比較と値まで一致。 -/
lemma coherentColimitApexPointedLongNativeComparison_heq_diagonal :
    HEq (coherentColimitApexPointedLongNativeComparison B T)
      (leftFibrationPrism_diagonalTransportIso p q g β h₀ h₁ P
        (coherentColimitApexPointedLongPrism_start B T)
        (coherentColimitApexPointedLongPrism_finish B T)
        ((coherentColimitApexPointedLongPrism_projection B T).trans
          (intervalMappingPoint_uncurry D l))) := by
  unfold coherentColimitApexPointedLongNativeComparison
  refine (functorIsoOfEq_heq _ _ _).trans ?_
  have h := fiberTransportPointComparison_heq_diagonal (K := A)
    (L := (Δ[0] : SSet.{u + 1})) p q D W l
  refine h.trans ?_
  exact leftFibrationPrism_diagonalTransportIso_heq_of_prism_eq p q
    (r ≫ (W).endpoint) g β h₀ h₁ ((Δ[1] ◁ r) ≫ (W).prism) P
    (fiberTransportFamily_point_prism_start p q (intervalMappingUncurry D) W l)
    (coherentColimitApexPointedLongPrism_start B T)
    (fiberTransportFamily_point_prism_finish p q (intervalMappingUncurry D) W l)
    (coherentColimitApexPointedLongPrism_finish B T)
    ((fiberTransportFamily_point_prism_projection p q (intervalMappingUncurry D) W l).trans
      (intervalMappingPoint_uncurry D l))
    ((coherentColimitApexPointedLongPrism_projection B T).trans
      (intervalMappingPoint_uncurry D l))
    (coherentColimitApexPointedLongTransport_point_prism B T l)

end SerrePositivity.InfinityCategories.F2
