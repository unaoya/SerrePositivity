module

public import SerrePositivity.InfinityCategories.F2.CoherentColimitApexPointedLongPrism
public import SerrePositivity.InfinityCategories.F2.PointedSingletonPrismFamily

/-!
概要：明示した元の全 pointed 族の長辺を、元の同じ長区間の輸送証人にする。
方針：同じ実 prism と元の実終点を、一点区間の全証人へ厳密に戻す。
規約：元の全係数・実両端・区間を保持。使われ方：元の長辺普遍比較との合成則。
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
local notation "s" => coherentColimitApexTriangle B T
local notation "A" => spaceSimplexPointedCoefficients s
local notation "q" => coherentColimitApexCoefficientMap B T
local notation "g" => coherentColimitApexTargetCoefficientMap B T
local notation "D" => SSet.yonedaEquiv.symm (coherentColimitRawIntervalVertex B d)

/-- 同じ全 pointed 族の長辺と実終点を保持した、元の同じ全長区間の輸送証人。 -/
def coherentColimitApexPointedLongTransport :
    FiberTransportFamily (b := (coherentDiagramTotalCocone J).vertex)
      pointedSpaceProjection q (intervalMappingUncurry D) :=
  pointedSingletonPrismFamily D q g (coherentColimitApexPointedLongPrism B T)
    (coherentColimitApexPointedLongPrism_start B T)
    (coherentColimitApexPointedLongPrism_finish B T)
    (coherentColimitApexPointedLongPrism_projection B T)

/-- 同じ証人の指定点の終点は、元の実終 fiber 内の同じ全係数作用そのもの。 -/
lemma coherentColimitApexPointedLongTransport_point_endpoint
    (v : (Δ[0] : SSet.{u + 1}) _⦋0⦌) :
    lift (𝟙 A) (SSet.const v) ≫ (coherentColimitApexPointedLongTransport B T).endpoint = g :=
  pointedSingletonPrismFamily_point_endpoint _ _ _ _ _ _ _ v

/-- 同じ証人の指定点の prism は、元の同じ全 pointed 三角形の長辺そのもの。 -/
lemma coherentColimitApexPointedLongTransport_point_prism
    (v : (Δ[0] : SSet.{u + 1}) _⦋0⦌) :
    (Δ[1] ◁ lift (𝟙 A) (SSet.const v)) ≫
      (coherentColimitApexPointedLongTransport B T).prism =
        coherentColimitApexPointedLongPrism B T :=
  pointedSingletonPrismFamily_point_prism _ _ _ _ _ _ _ v

end SerrePositivity.InfinityCategories.F2
