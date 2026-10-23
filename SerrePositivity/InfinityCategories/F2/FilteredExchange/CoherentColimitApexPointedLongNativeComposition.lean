module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.PointedIntervalUniversalSourceComposition
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentColimitApexPointedLongComparison
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.FunctorIsoDownHorizontal

/-!
概要：元の全実長辺の比較と指定一点普遍比較を、同じ全普遍輸送への直接比較へ合成する。
方針：元の初期値 q と元の長辺証人を一般の初期値上の指定合成式へ代入する。
規約：元の長区間・全係数・指定値を保持。使われ方：native 長辺の値比較への照合。
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
local notation "γ" => intervalMappingUncurry D
local notation "U" => parametrizedTransportPullbackFamily p γ
  (intervalMappingUncurry_zero D) (intervalMappingUncurry_one D)
local notation "W" => coherentColimitApexPointedLongTransport B T
local notation "e" => FunctorIso.precomp (pointedIntervalTransportAt_universalIso D l) q

/-- 元の実長辺と同じ全普遍輸送の元の初期値 q による制限との直接の指定比較。 -/
def coherentColimitApexPointedLongNativeComparison :
    FunctorIso g (q ≫ (functorVertexEquiv _ _).symm
      ((parametrizedFiberTransport p _ _).app (Opposite.op ⦋0⦌)
        ((D).app (Opposite.op ⦋0⦌) l))) :=
  functorIsoOfEq ((FiberTransportFamily.endpointIso p (q ≫ 𝟙 _) γ
    (intervalMappingUncurry_one D) W ((U).precomposeSource q)).precomp r)
    (coherentColimitApexPointedLongTransport_point_endpoint B T l)
    (by rw [fiberTransportFamily_precomposeSource_point_endpoint,
      pointedParametrizedTransportPullback_point_endpoint])

/-- 元の長辺比較と指定一点普遍比較の合成は、同じ二実 prism の直接比較そのもの。 -/
lemma coherentColimitApexPointedLongComparison_trans_universal :
    coherentColimitApexPointedLongComparison B T ≪≫ e =
      coherentColimitApexPointedLongNativeComparison B T := by
  let w : FiberTransportFamily p q γ := W
  have h := pointedIntervalUniversalSource_comparison_trans
    (C := (Δ[0] : SSet.{u + 1})) (K := A)
    (x := (coherentDiagramTotalCocone F).vertex)
    (y := (coherentDiagramTotalCocone J).vertex) D l q w
  have ht : q ≫ (functorVertexEquiv _ _).symm
      ((parametrizedFiberTransport p _ _).app (Opposite.op ⦋0⦌)
        ((D).app (Opposite.op ⦋0⦌) l)) = r ≫ ((U).precomposeSource q).endpoint := by
    rw [fiberTransportFamily_precomposeSource_point_endpoint,
      pointedParametrizedTransportPullback_point_endpoint]
  have hn := congrArg (fun v => functorIsoOfEq v
    (coherentColimitApexPointedLongTransport_point_endpoint B T l) ht.symm) h
  rw [functorIsoOfEq_trans
    (hg := coherentColimitRawUniversalTriangleComparison_target B (d := d) q)] at hn
  have hc : functorIsoOfEq (functorIsoOfEq e
      (pointedIntervalTransportAt_pre D l q).symm
      ht) (coherentColimitRawUniversalTriangleComparison_target B (d := d) q) ht.symm = e :=
    eq_of_heq ((functorIsoOfEq_heq _ _ _).trans (functorIsoOfEq_heq _ _ _))
  rw [hc] at hn
  exact hn

end SerrePositivity.InfinityCategories.F2
