module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.ConstantDiagramTrianglePointComparison
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.ConstantTargetTriangleVertexComponent
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.UnstraighteningTriangleFamilyPostComponent
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentColimitConstantTriangleLongEndpoint

/-!
概要：元の定値余極限三角形の全空間比較の fiber 像を、同じ長辺輸送比較へ戻す。
方針：元の三辺の rawInterval 表示と同じ全三角形の一点比較を合成する。
規約：元の三辺・全三角形・指定長辺比較を保持。使われ方：下側輸送因子の消去。
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

/-- 元の三角形比較の fiber 像は、同じ元の長辺輸送への比較の同じ一点制限。 -/
lemma coherentColimitConstantTriangleFiberComparison_heq_transport :
    HEq ((unstraighteningTriangleVertexIso
      (SSet.const z₀ : ((SSet.uliftFunctor.{u + 1, u}).obj B) ⟶ SpaceInfinity)
      (SSet.const z₁) (SSet.const z₃) A R C
      (V).diagram (V).first (V).second (V).long).postcomp
        (constantUnstraighteningFiberProjection ((SSet.uliftFunctor.{u + 1, u}).obj B) z₃))
      (((constantDiagramTransportWitness
        (constantDiagramMappingFamilyWitness ((SSet.uliftFunctor.{u + 1, u}).obj B) C₀)).endpointIso
        pointedSpaceProjection
        (constantUnstraighteningFiberProjection ((SSet.uliftFunctor.{u + 1, u}).obj B) z₀)
        (intervalMappingUncurry C₀) (intervalMappingUncurry_one C₀)
        (coherentColimitConstantTriangleLongTransport B T)).precomp
          (lift (𝟙 _) (SSet.const l))) := by
  have ha := (coherentColimitRawIntervalVertex_constant B a).trans
    (SSet.yonedaEquiv_symm_zero A)
  have hb := (coherentColimitRawIntervalVertex_constant B b).trans
    (SSet.yonedaEquiv_symm_zero R)
  have hc := (coherentColimitRawIntervalVertex_constant B c).trans
    (SSet.yonedaEquiv_symm_zero C)
  refine (constantTargetTriangleVertexIso_heq_component _ _ z₃ A R C
    (V).diagram (V).first (V).second (V).long).trans ?_
  refine (unstraighteningMappingTriangleIso_postcomp_app_heq_of_family_eq
    _ _ _ (SSet.const A) _ (SSet.const R) _ (SSet.const C) _ (V).diagram
    ha.symm hb.symm hc.symm (V).first (V).second (V).long
    (coherentColimitConstantTriangle_first_rawInterval B T)
    (coherentColimitConstantTriangle_last_rawInterval B T)
    (coherentColimitConstantTriangle_long_rawInterval B T) _ l).trans ?_
  exact constantDiagramTriangleComparison_app_heq_transport A₀ R₀ C₀ (V).diagram
    (coherentColimitConstantTriangle_first_rawInterval B T)
    (coherentColimitConstantTriangle_last_rawInterval B T)
    (coherentColimitConstantTriangle_long_rawInterval B T) l

end SerrePositivity.InfinityCategories.F2
