module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitConstantTriangleFaces
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.ConstantDiagramTriangleTransport

/-!
概要：元の定値余極限三角形の指定長辺証拠を、元の長区間の全輸送として保持する。
方針：元の三面を同じ三つの全区間族で照合し、同じ全三角形の長辺を取り出す。
規約：元の持ち上げの指定値を保持。使われ方：元の下側輸送因子の長辺での整合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable (B : SSet.{u})
  {F G J : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}}
  {a : SSet.Homotopy F G} {b : SSet.Homotopy G J} {c : SSet.Homotopy F J}
  (T : FunctorCompositionTriangle a b c)
local notation "z₀" => JoinCocone.vertex (coherentDiagramTotalCocone F)
local notation "z₃" => JoinCocone.vertex (coherentDiagramTotalCocone J)
local notation "H" => CoherentTransformationVertexTriangle.diagram
  (coherentTriangleOfFunctorTriangle (coherentColimitConstantTriangle B T))
local notation "A" => SSet.yonedaEquiv.symm (coherentColimitRawIntervalVertex B a)
local notation "R" => SSet.yonedaEquiv.symm (coherentColimitRawIntervalVertex B b)
local notation "C" => SSet.yonedaEquiv.symm (coherentColimitRawIntervalVertex B c)

/-- 元の定値余極限三角形の長辺を、元の長区間の同じ全輸送として保持する。 -/
def coherentColimitConstantTriangleLongTransport :
    FiberTransportFamily (b := z₃) pointedSpaceProjection
      (constantUnstraighteningFiberProjection ((SSet.uliftFunctor.{u + 1, u}).obj B) z₀)
      (intervalMappingUncurry C) :=
  constantDiagramTriangleLongTransport A R C H
    (coherentColimitConstantTriangle_first_rawInterval B T)
    (coherentColimitConstantTriangle_last_rawInterval B T)
    (coherentColimitConstantTriangle_long_rawInterval B T)

/-- 元の定値長辺の比較は、同じ元の余極限三角形の長辺輸送を経由して値を保つ。 -/
lemma coherentColimitConstantTransportIso_heq_triangle :
    HEq (constantDiagramMappingTransportIso ((SSet.uliftFunctor.{u + 1, u}).obj B) C)
      ((constantDiagramTransportWitness
        (constantDiagramMappingFamilyWitness ((SSet.uliftFunctor.{u + 1, u}).obj B) C)).endpointIso
        pointedSpaceProjection
        (constantUnstraighteningFiberProjection ((SSet.uliftFunctor.{u + 1, u}).obj B) z₀)
        (intervalMappingUncurry C) (intervalMappingUncurry_one C)
        (coherentColimitConstantTriangleLongTransport B T) ≪≫
          pointedIntervalTransportComparison
            (constantUnstraighteningFiberProjection ((SSet.uliftFunctor.{u + 1, u}).obj B) z₀) C
            (coherentColimitConstantTriangleLongTransport B T)) :=
  constantDiagramMappingTransportIso_heq_triangle A R C H
    (coherentColimitConstantTriangle_first_rawInterval B T)
    (coherentColimitConstantTriangle_last_rawInterval B T)
    (coherentColimitConstantTriangle_long_rawInterval B T)

end SerrePositivity.InfinityCategories.F2
