module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitApexPointedLongComparison
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.PointedIntervalComparisonComposition
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FunctorIsoDownHorizontal
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FunctorIsoWhiskerAlgebra

/-!
概要：明示した元の長辺と元の普遍三角形の長辺との比較を、元の普遍比較へ合成する。
方針：同じ全長区間の endpointIso の合成則を指定一点で評価する。
規約：元の全係数と指定普遍比較を保持。使われ方：全三角形の終点像との照合。
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
local notation "W" => coherentColimitApexPointedLongTransport B T
local notation "U" => coherentColimitRawUniversalTriangleLongTransport B T q

/-- 元の二つの実長辺の指定比較を、同じ実終 fiber の二射の同型にする。 -/
def coherentColimitApexPointedLongEndpointComparison :
    FunctorIso g ((q ≫ coherentColimitRawFiberTransport B a) ≫
      coherentColimitRawFiberTransport B b) :=
  functorIsoOfEq ((FiberTransportFamily.endpointIso pointedSpaceProjection q
    (intervalMappingUncurry D) (intervalMappingUncurry_one D) W U).precomp r)
    (coherentColimitApexPointedLongTransport_point_endpoint B T l)
    (coherentColimitRawUniversalTriangleLongTransport_point_endpoint B T q l)

/-- 同じ二実長辺の比較と元の普遍比較の合成は、明示した実長辺の普遍比較に等しい。 -/
lemma coherentColimitApexPointedLongEndpointComparison_trans :
    coherentColimitApexPointedLongEndpointComparison B T ≪≫
      coherentColimitRawUniversalTriangleComparison B T q =
        coherentColimitApexPointedLongComparison B T := by
  have h := congrArg (fun e => FunctorIso.precomp e r)
    (pointedIntervalTransportComparison_trans q D W U)
  rw [functorIso_precomp_trans] at h
  have hn := congrArg
    (fun e => functorIsoOfEq e
      (coherentColimitApexPointedLongTransport_point_endpoint B T l)
      (coherentColimitRawUniversalTriangleComparison_target B (d := d) q)) h
  rw [functorIsoOfEq_trans
    (hg := coherentColimitRawUniversalTriangleLongTransport_point_endpoint B T q l)] at hn
  exact hn

end SerrePositivity.InfinityCategories.F2
