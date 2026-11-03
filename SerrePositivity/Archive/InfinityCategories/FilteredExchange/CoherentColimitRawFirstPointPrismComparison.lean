module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitConstantTransportRawPoint
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FiberTransportRestrictedPrismComparison
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.PointedIntervalTransportSource

/-!
概要：元の定値第一辺と同じ raw 普遍第一辺の一点 prism 比較を、元の指定一点比較に同定する。
方針：元の二全輸送の endpointIso と同じ指定点の制限を保持する。
規約：実両端を計算し、指定比較を再選択しない。使われ方：全第一辺終点比較の値の回収。
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
  {F G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}} (a : SSet.Homotopy F G)
local notation "P" => coherentColimitRawConstantFiberProjection B F
local notation "A" => SSet.yonedaEquiv.symm (coherentColimitRawIntervalVertex B a)
local notation "l" => stdSimplex.obj₀Equiv.symm (0 : Fin 1)
local notation "s" => lift (𝟙 _) (SSet.const l)
local notation "w" => constantDiagramTransportWitness
  (constantDiagramMappingFamilyWitness (CategoryTheory.Functor.obj SSet.uliftFunctor B) A)
local notation "U" => pointedIntervalTransportSource P A

/-- 元の二つの第一辺の同じ一点 prism 比較を、同じ実両端で保持する。 -/
def coherentColimitRawFirstPointPrismComparison :=
  functorIsoOfEq (fiberTransportRestrictedPrismComparison pointedSpaceProjection P
    (intervalMappingUncurry A) (intervalMappingUncurry_one A) w U s)
    (coherentColimitConstantTransport_endpoint_point B l)
    (coherentColimitConstantTransport_raw_point_target B a)

/-- 同じ実両端の第一辺 prism 比較は、元の同じ指定 raw 一点比較そのもの。 -/
lemma coherentColimitRawFirstPointPrismComparison_eq_point :
    coherentColimitRawFirstPointPrismComparison B a =
      coherentColimitConstantTransportRawPointIso B a := by
  have he := fiberTransportRestrictedPrismComparison_eq_endpointIso pointedSpaceProjection P
    (intervalMappingUncurry A) (intervalMappingUncurry_one A) w U s
  have hs := congrArg (fun e => e.precomp s) (pointedIntervalTransportComparison_eq_source P A w)
  have hp : HEq (coherentColimitConstantTransportRawPointIso B a)
      ((pointedIntervalTransportComparison P A w).precomp s) :=
    (coherentColimitConstantTransportRawPointIso_heq_point B a).trans
      ((heq_of_eq (coherentColimitConstantTransportPointIso_eq_witness B a)).trans
        (functorIsoOfEq_heq _ _ _))
  exact eq_of_heq ((functorIsoOfEq_heq _ _ _).trans
    ((heq_of_eq he).trans ((heq_of_eq hs).symm.trans hp.symm)))

end SerrePositivity.InfinityCategories.F2
