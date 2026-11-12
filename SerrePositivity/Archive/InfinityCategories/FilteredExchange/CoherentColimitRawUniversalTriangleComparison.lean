module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitRawUniversalTriangleLongTransport
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FunctorIsoTransport

/-!
概要：元の余極限二単体上で、元の二つの raw 普遍輸送を辺に持つ全三角形を充填する。
方針：同じ普遍 prism の実中間点と元の二面式を使う。
規約：全係数・初期値・元の全二単体を保持。使われ方：新長辺残余の普遍三角形への照合。
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
  (T : FunctorCompositionTriangle a b d) {K : SSet.{u + 1}}
  (f : K ⟶ vertexFiber pointedSpaceProjection (JoinCocone.vertex (coherentDiagramTotalCocone F)))
local notation "H₀₁" => coherentColimitRawTransportPointPrism B a f
local notation "H₁₂" => coherentColimitRawTransportPointPrism B b
  (f ≫ coherentColimitRawFiberTransport B a)
local notation "β" => fst Δ[2] K ≫ FunctorCompositionTriangle.diagram T ≫ coherentColimitFunctor B

local notation "D" => SSet.yonedaEquiv.symm (coherentColimitRawIntervalVertex B d)
local notation "q" => fst K (Δ[0] : SSet)
local notation "g" => (f ≫ coherentColimitRawFiberTransport B a) ≫
  coherentColimitRawFiberTransport B b

local notation "l" => stdSimplex.obj₀Equiv.symm (0 : Fin 1)
local notation "s" => lift (𝟙 K) (SSet.const l)

/-- 元の長区間の同じ指定点の普遍終点は、元の長辺 raw 普遍輸送の前合成そのもの。 -/
lemma coherentColimitRawUniversalTriangleComparison_target :
    s ≫ (f ▷ Δ[0]) ≫ (pointedIntervalTransport D).endpoint =
      f ≫ coherentColimitRawFiberTransport B d :=
  pointedIntervalTransportAt_pre D l f

/-- 同じ元の全二単体と二普遍辺から得た、三つの raw 普遍輸送の指定合成比較。 -/
def coherentColimitRawUniversalTriangleComparison :
    FunctorIso g (f ≫ coherentColimitRawFiberTransport B d) :=
  functorIsoOfEq ((pointedIntervalTransportComparison f D
    (coherentColimitRawUniversalTriangleLongTransport B T f)).precomp s)
    (coherentColimitRawUniversalTriangleLongTransport_point_endpoint B T f l)
    (coherentColimitRawUniversalTriangleComparison_target B (d := d) f)

/-- 同じ実両端の合成比較は、同じ元の全長辺輸送の指定普遍比較の一点値。 -/
lemma coherentColimitRawUniversalTriangleComparison_heq_pointed :
    HEq (coherentColimitRawUniversalTriangleComparison B T f)
      ((pointedIntervalTransportComparison f D
        (coherentColimitRawUniversalTriangleLongTransport B T f)).precomp s) :=
  functorIsoOfEq_heq _ _ _

end SerrePositivity.InfinityCategories.F2
