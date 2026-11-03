module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitUpperAction
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentTotalMapNativeTransport
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentTotalMapNativeValue

/-!
概要：余極限関手の指定辺と a6 の指定 native 写像の実際の輸送を比較する。
方針：同じ対角の上下三角形の作用比較を合成し、元の余錐の前合成同値で反映する。
規約：元の二輸送を保持。使われ方：余極限関手の全錐の像と a6 の native 錐の比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.F2
attribute [local instance] vertexFiber_kanComplex_of_leftFibration
variable (B : SSet.{u})
  {F G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}} (H : SSet.Homotopy F G)

/-- 指定余極限辺と a6 の指定 native 写像の輸送は、元の標的の値で同型に比較される。 -/
def coherentColimitFiberTransportComparisonIso :
    FunctorIso (coherentColimitFiberTransport B H ≫
      (pointedSpaceFiberValueEquivalence (coherentDiagramTotalVertex G)).hom)
      (coherentTotalMapNativeFiberTransport F G
        (coherentTransformationTotalMap F G (coherentVertexOfHomotopy H)) ≫
          (pointedSpaceFiberValueEquivalence (coherentDiagramTotalVertex G)).hom) := by
  have e := (coherentColimitLowerActionIso B H).symm ≪≫ coherentColimitUpperActionIso B H
  rw [coherentTotalMapNativeAction_eq] at e
  have hp := (coherentTotalCoconeFiber_value_pre_homotopyEquivalence F
    (spaceInfinityObject (coherentDiagramTotalVertex G)).obj).isQCatEquivalence
  exact hp.isFullyFaithful.preimageVertexIso e

/-- 値への後合成同値の充満忠実性で、元の両 fiber 間の実際の二輸送を比較する。 -/
def coherentColimitFiberTransportIso : FunctorIso (coherentColimitFiberTransport B H)
    (coherentTotalMapNativeFiberTransport F G
      (coherentTransformationTotalMap F G (coherentVertexOfHomotopy H))) := by
  have hp := ((pointedSpaceFiberValueEquivalence (coherentDiagramTotalVertex G)).postcompose
    (vertexFiber pointedSpaceProjection (coherentDiagramTotalCocone F).vertex)).isQCatEquivalence
  exact hp.isFullyFaithful.preimageVertexIso (coherentColimitFiberTransportComparisonIso B H)

/-- 元の余極限の指定辺の輸送を、元の始域と終域の Kan 値の間で表示する。 -/
def coherentColimitTransportValue :=
  (coherentTotalSourceValueEquivalence F).inv ≫ coherentColimitFiberTransport B H ≫
    (pointedSpaceFiberValueEquivalence (coherentDiagramTotalVertex G)).hom

/-- 元の余極限関手の指定辺の値は、a6 で使う元の具体的 Kan 頂点射と同型。 -/
def coherentColimitTransportValueIso : FunctorIso (coherentColimitTransportValue B H)
    ((SSet.uliftFunctor.{u + 1, u}).map (coherentTotalVertexMap F G
      (coherentTransformationTotalMap F G (coherentVertexOfHomotopy H)))) :=
  ((coherentColimitFiberTransportComparisonIso B H).precomp
    (coherentTotalSourceValueEquivalence F).inv) ≪≫
      coherentTotalMapNativeValueIso F G
        (coherentTransformationTotalMap F G (coherentVertexOfHomotopy H))

end SerrePositivity.InfinityCategories.F2
