module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitApexPointedLongComposition
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitApexPointedEndpointComparisons
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.SpaceTrianglePointedLongEndpoint
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FiberTransportRestrictedPrismComparison
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.RelativeExtensionFiberEndpointDataEquality

/-!
概要：同じ全三角形の終点像と、元の同じ長辺輸送の終点比較を厳密に同定する。
方針：長辺延長空間への制限で、底・始点・実二 prism と実二終点を揃える。
規約：元の全係数と指定比較を保持。使われ方：元の普遍三角形比較との合成。
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
local notation "D" => SSet.yonedaEquiv.symm (coherentColimitRawIntervalVertex B d)
local notation "l" => stdSimplex.obj₀Equiv.symm (0 : Fin 1)
local notation "r" => lift (𝟙 A) (SSet.const l)
local notation "W" => coherentColimitApexPointedLongTransport B T
local notation "U" => coherentColimitRawUniversalTriangleLongTransport B T q

/-- 同じ全三角形の終点像は、同じ実長辺輸送の指定終点比較に厳密に一致する。 -/
lemma coherentColimitApexPointedTargetEndpointIso_eq_longEndpointComparison :
    coherentColimitApexPointedTargetEndpointIso B T =
      coherentColimitApexPointedLongEndpointComparison B T := by
  unfold coherentColimitApexPointedTargetEndpointIso
  rw [spaceTrianglePointedFamilyEndpointIso_eq_long_witnessIso]
  unfold coherentColimitApexPointedLongEndpointComparison
  refine eq_of_heq (HEq.trans ?_ (functorIsoOfEq_heq _ _ _).symm)
  rw [← fiberTransportRestrictedPrismComparison_eq_endpointIso]
  unfold fiberTransportRestrictedPrismComparison
  apply relativeExtensionFiberEndpoint_witnessIso_heq_of_dataEq
  · calc
      _ = coherentColimitApexPointedLongPrism B T ≫ pointedSpaceProjection := by
        rw [coherentColimitApexPointedLongPrism, Category.assoc,
          spaceSimplexPointedFamily_projection]
      _ = ((Δ[1] ◁ r) ≫ FiberTransportFamily.prism W) ≫ pointedSpaceProjection :=
        congrArg (fun z => z ≫ pointedSpaceProjection)
          (coherentColimitApexPointedLongTransport_point_prism B T l).symm
      _ = _ := by rw [Category.assoc, FiberTransportFamily.over_base W]
  · rw [coherentColimitApexCoefficientMap_ι]
    simp only [simplexPrismVertex, ← Category.assoc, lift_fst, lift_snd, Category.id_comp]
  · exact (coherentColimitApexPointedLongTransport_point_prism B T l).symm
  · exact (coherentColimitRawUniversalTriangleLongTransport_point_prism B T q l).symm
  · exact (coherentColimitApexPointedLongTransport_point_endpoint B T l).symm
  · exact (coherentColimitRawUniversalTriangleLongTransport_point_endpoint B T q l).symm

/-- 元の全三角形の終点像と元の普遍比較は、明示した同じ実長辺の普遍比較へ合成する。 -/
lemma coherentColimitApexPointedTargetEndpointIso_trans_universal :
    coherentColimitApexPointedTargetEndpointIso B T ≪≫
      coherentColimitRawUniversalTriangleComparison B T q =
        coherentColimitApexPointedLongComparison B T := by
  rw [coherentColimitApexPointedTargetEndpointIso_eq_longEndpointComparison]
  exact coherentColimitApexPointedLongEndpointComparison_trans B T

end SerrePositivity.InfinityCategories.F2
