module

public import SerrePositivity.InfinityCategories.Core.Equivalence
public import SerrePositivity.InfinityCategories.Core.EquivalenceCalculus
public import SerrePositivity.InfinityCategories.Core.FunctorEvaluation
public import SerrePositivity.InfinityCategories.Core.InnerFiber
public import SerrePositivity.InfinityCategories.Core.PrecompositionEquivalence
public import SerrePositivity.InfinityCategories.Core.PrismContraction
public import SerrePositivity.InfinityCategories.Core.VertexFiber
public import SerrePositivity.InfinityCategories.Core.VertexFiberNervePullback
public import SerrePositivity.InfinityCategories.F1.Categories.CatInfinity
public import SerrePositivity.InfinityCategories.F1.Categories.PointedSpaces
public import SerrePositivity.InfinityCategories.F1.Coherent.Vertices
public import SerrePositivity.InfinityCategories.F1.Fibrations.CartesianFibration
public import SerrePositivity.InfinityCategories.F1.MappingSpaces.IntervalMappingSpace
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.LeftUnstraighteningFiberValue
public import SerrePositivity.InfinityCategories.F1.Transport.ParametrizedFiberTransport
public import SerrePositivity.InfinityCategories.F1.Universe.InnerFibration
public import SerrePositivity.InfinityCategories.F1.Universe.Kan
public import SerrePositivity.InfinityCategories.F1.Yoneda.CanonicalYonedaFiberTransport
public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.PresheafDensityEvaluation
public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafUnstraightening
public import SerrePositivity.InfinityCategories.F1.Yoneda.YonedaInfinityConstruction
public import SerrePositivity.InfinityCategories.F1.Ind.CanonicalIntervalYonedaValue
public import SerrePositivity.InfinityCategories.F1.Ind.DensityIdentityEndpointEquivalence
public import SerrePositivity.InfinityCategories.F1.Ind.DensityIdentityLift
public import SerrePositivity.InfinityCategories.F1.Ind.DensityIdentityLiftBase
public import SerrePositivity.InfinityCategories.F1.Ind.ElementsYonedaSliceInterval
public import SerrePositivity.InfinityCategories.F1.Ind.PointPrismTransportComparison

/-!
概要：元の canonical な密度輸送の全 fiber 値写像は同値。
方針：同じ始値・同じ底を持つ元の密度持ち上げと普遍輸送の終値を比較する。
規約：元の指定写像の同値性を証明し、新しい同値性仮定を入力しない。
使われ方：元の Yoneda comma 比較の実際の値写像の同値性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
attribute [local instance] vertexFiber_kanComplex_of_leftFibration
variable {C : SSet.{u}} [Quasicategory C]
  (F : (SSet.uliftFunctor.{u + 1, u}).obj C.op ⟶ SpaceInfinity.{u}) (x : C _⦋0⦌)
local notation "z" => F.app (Opposite.op ⦋0⦌) (ULift.up (SSet.opObjEquiv.symm x))

/-- 元の持ち上げの同じ終値と、元の canonical な普遍輸送の終値の全 fiber 上の比較。 -/
def presheafDensityIdentityLiftEndpointTransportIso :
    FunctorIso (presheafDensityIdentityLiftEndpointAtValue F x)
      (presheafDensityCanonicalFiberInterval F x ≫
        parametrizedFiberTransport pointedSpaceProjection
          (presheafDensityCanonicalSourceValue x) z ≫
        evaluateFunctorAt (canonicalYonedaPointedIdentity x)) := by
  apply pointPrismTransportIso pointedSpaceProjection (canonicalYonedaPointedIdentity x)
    (presheafDensityCanonicalFiberInterval F x) (presheafDensityIdentityLiftPrism F x)
    (presheafDensityIdentityLiftEndpointAtValue F x)
  · exact presheafDensityIdentityLiftPrism_start F x
  · rw [presheafDensityIdentityLiftEndpointAtValue, Category.assoc,
      vertexFiberTransport_ι pointedSpaceProjection (presheafDensityEvaluationVertex_value F x),
      presheafDensityIdentityLiftPrism_finish]
  · exact presheafDensityIdentityLiftPrism_projection F x

/-- 元の canonical な輸送の同じ全 fiber 値写像自身が同値。 -/
lemma presheafDensityCanonicalTransportValue_isQCatEquivalence :
    IsQCatEquivalence (presheafDensityCanonicalTransportValue F x) := by
  have ht : IsQCatEquivalence (presheafDensityCanonicalFiberInterval F x ≫
      parametrizedFiberTransport pointedSpaceProjection (presheafDensityCanonicalSourceValue x) z ≫
      evaluateFunctorAt (canonicalYonedaPointedIdentity x)) :=
    (presheafDensityIdentityLiftEndpointAtValue_isQCatEquivalence F x).ofFunctorIso
      (presheafDensityIdentityLiftEndpointTransportIso F x)
  simpa only [presheafDensityCanonicalTransportValue, Category.assoc] using
    ht.comp (pointedSpaceFiberValueEquivalence z).isQCatEquivalence

end SerrePositivity.InfinityCategories.F2.Ind
