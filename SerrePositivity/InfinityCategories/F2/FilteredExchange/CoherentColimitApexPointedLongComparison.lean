module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentColimitApexPointedLongTransport
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentColimitRawUniversalTriangleComparison

/-!
概要：元の全 pointed 族の長辺から、同じ長区間の普遍比較を独立に構成する。
方針：実長辺の輸送証人の普遍比較を、元の指定一点で評価する。
規約：元の長辺と全係数を保持。使われ方：全三角形の終点比較との合成則。
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
local notation "l" => stdSimplex.obj₀Equiv.symm (0 : Fin 1)
local notation "r" => lift (𝟙 A) (SSet.const l)

/-- 元の明示した実長辺から得た、元の同じ長区間の指定普遍比較。 -/
def coherentColimitApexPointedLongComparison :
    FunctorIso g (q ≫ coherentColimitRawFiberTransport B d) :=
  functorIsoOfEq ((pointedIntervalTransportComparison q D
    (coherentColimitApexPointedLongTransport B T)).precomp r)
    (coherentColimitApexPointedLongTransport_point_endpoint B T l)
    (coherentColimitRawUniversalTriangleComparison_target B (d := d) q)

/-- 同じ比較は、元の実長辺の全輸送証人の普遍比較の指定一点像を保持する。 -/
lemma coherentColimitApexPointedLongComparison_heq_pointed :
    HEq (coherentColimitApexPointedLongComparison B T)
      ((pointedIntervalTransportComparison q D
        (coherentColimitApexPointedLongTransport B T)).precomp r) :=
  functorIsoOfEq_heq _ _ _

end SerrePositivity.InfinityCategories.F2
