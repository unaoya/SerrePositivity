module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitConstantTriangleFiberComparison
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitConstantTransportPointEndpoints
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FunctorIsoTransport

/-!
概要：元の定値余極限三角形比較の fiber 像を、同じ実両端上の輸送比較へ厳密に同定する。
方針：元の一点比較と元の実終点の等式による表示変更だけを合成する。
規約：元の指定値を保持。使われ方：元の三角形比較を逆合成して輸送因子を消去する。
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
  {a : SSet.Homotopy F G} {b : SSet.Homotopy G J} {c : SSet.Homotopy F J}
  (T : FunctorCompositionTriangle a b c)
local notation "z₀" => JoinCocone.vertex (coherentDiagramTotalCocone F)
local notation "z₁" => JoinCocone.vertex (coherentDiagramTotalCocone G)
local notation "z₃" => JoinCocone.vertex (coherentDiagramTotalCocone J)
local notation "V" => coherentTriangleOfFunctorTriangle (coherentColimitConstantTriangle B T)
local notation "A" => coherentVertexOfHomotopy
  (simplicialHomotopyOfFunctorEdge (coherentColimitConstantEdge B a))
local notation "R" => coherentVertexOfHomotopy
  (simplicialHomotopyOfFunctorEdge (coherentColimitConstantEdge B b))
local notation "C" => coherentVertexOfHomotopy
  (simplicialHomotopyOfFunctorEdge (coherentColimitConstantEdge B c))
local notation "A₀" => SSet.yonedaEquiv.symm (coherentColimitRawIntervalVertex B a)
local notation "R₀" => SSet.yonedaEquiv.symm (coherentColimitRawIntervalVertex B b)
local notation "C₀" => SSet.yonedaEquiv.symm (coherentColimitRawIntervalVertex B c)
local notation "l" => stdSimplex.obj₀Equiv.symm (0 : Fin 1)

/-- 元の定値余極限三角形の全空間比較の同じ fiber 像。 -/
def coherentColimitConstantTriangleFiberIso :=
  (unstraighteningTriangleVertexIso
    (SSet.const z₀ : ((SSet.uliftFunctor.{u + 1, u}).obj B) ⟶ SpaceInfinity)
    (SSet.const z₁) (SSet.const z₃) A R C
    (V).diagram (V).first (V).second (V).long).postcomp
      (constantUnstraighteningFiberProjection ((SSet.uliftFunctor.{u + 1, u}).obj B) z₃)

/-- 元の実両端へ戻した輸送比較は、元の全空間三角形比較の同じ fiber 像に等しい。 -/
lemma coherentColimitConstantTriangleFiberIso_eq_transport :
    coherentColimitConstantTriangleFiberIso B T =
      functorIsoOfEq (((constantDiagramTransportWitness
        (constantDiagramMappingFamilyWitness ((SSet.uliftFunctor.{u + 1, u}).obj B) C₀)).endpointIso
        pointedSpaceProjection
        (constantUnstraighteningFiberProjection ((SSet.uliftFunctor.{u + 1, u}).obj B) z₀)
        (intervalMappingUncurry C₀) (intervalMappingUncurry_one C₀)
        (coherentColimitConstantTriangleLongTransport B T)).precomp
          (lift (𝟙 _) (SSet.const l)))
        (coherentColimitConstantTransport_endpoint_point B l)
        (coherentColimitConstantTriangleLongTransport_endpoint_point B T l) := by
  exact eq_of_heq ((coherentColimitConstantTriangleFiberComparison_heq_transport B T).trans
    (functorIsoOfEq_heq _ _ _).symm)

end SerrePositivity.InfinityCategories.F2
