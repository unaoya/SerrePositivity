module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitRawFirstChoiceTriangleComparison
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FiberTransportFamilyMapIsoApp

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
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable (B : SSet.{u})
  {F G J : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}}
  {a : SSet.Homotopy F G} {b : SSet.Homotopy G J} {d : SSet.Homotopy F J}
  (T : FunctorCompositionTriangle a b d) {K : SSet.{u + 1}}
  (f : K ⟶ vertexFiber pointedSpaceProjection (JoinCocone.vertex (coherentDiagramTotalCocone F)))
local notation "Q" => coherentColimitRawFirstChoiceSpace B a f
local notation "H₀₁" => coherentColimitRawFirstChoicePrism B a f
local notation "H₁₂" => coherentColimitRawTransportPointPrism B b
  (coherentColimitRawFirstChoiceEndpoint B a f)
local notation "β" => fst Δ[2] (K ⊗ Q) ≫
  FunctorCompositionTriangle.diagram T ≫ coherentColimitFunctor B

local notation "D" => SSet.const (coherentColimitRawIntervalVertex B d)

local notation "m" => curry (coherentColimitRawFirstChoiceEndpoint B a f) ≫
  CategoryTheory.Functor.map (ihom K) (coherentColimitRawFiberTransport B b)
local notation "c" => SSet.const (functorVertex (f ≫ coherentColimitRawFiberTransport B d))

/-- 元の全長辺比較の同じ指定成分は、元の二実輸送 prism の同じ係数制限の指定比較。 -/
lemma coherentColimitRawFirstChoiceTriangleComparisonApp_heq_restricted
    (x : (coherentColimitRawFirstChoiceSpace B a f) _⦋0⦌) :
    HEq (coherentColimitRawFirstChoiceTriangleComparisonApp B T f x)
      (fiberTransportRestrictedPrismComparison pointedSpaceProjection f
        (intervalMappingUncurry (D : Q ⟶ _)) (intervalMappingUncurry_one D)
        (coherentColimitRawFirstChoiceTriangleLongTransport B T f)
        (coherentColimitRawConstantEdgeTransport B d f Q) (lift (𝟙 K) (SSet.const x))) := by
  have := (coherentColimitRawFirstChoiceSpace_isContractibleKan B a f).kanComplex
  have := vertexFiber_kanComplex_of_leftFibration pointedSpaceProjection
    (JoinCocone.vertex (coherentDiagramTotalCocone J))
  let e := FiberTransportFamily.mapIso pointedSpaceProjection f
    (intervalMappingUncurry (D : Q ⟶ _)) (intervalMappingUncurry_one D)
    (coherentColimitRawFirstChoiceTriangleLongTransport B T f)
    (coherentColimitRawConstantEdgeTransport B d f Q)
  have h := functorIso_app_heq_of_heq (coherentColimitRawFirstChoiceTriangleComparison B T f) e
    (coherentColimitRawFirstChoiceTriangleLongTransport_map B T f).symm
    (coherentColimitRawConstantEdgeTransport_map B d f Q).symm
    (functorIsoOfEq_heq _ _ _) x
  exact h.trans (fiberTransportFamilyMapIsoApp_heq_restricted pointedSpaceProjection f
    (intervalMappingUncurry (D : Q ⟶ _)) (intervalMappingUncurry_one D)
    (coherentColimitRawFirstChoiceTriangleLongTransport B T f)
    (coherentColimitRawConstantEdgeTransport B d f Q) x)

end SerrePositivity.InfinityCategories.F2
