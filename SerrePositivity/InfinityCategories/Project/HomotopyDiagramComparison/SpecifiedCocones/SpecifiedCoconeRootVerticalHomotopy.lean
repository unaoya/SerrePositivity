module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SpecifiedCocones.SpecifiedCoconeRootClosingHomotopy
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SliceTransport.PointTransportEndpointFibration
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SliceTransport.NullEndpointEdge
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.KanExtensions.FixedExtensionEdgeHomotopy

/-!
概要：元の左右の根辺図式を、底・始点・終点を全時刻で固定する円柱で結ぶ。
方針：四因子相殺で恒等の類を持つ終点辺を、同じ両端の厳密な fiber 辺へ直して展開する。
規約：同じ元の二図式を保持する。使われ方：固定終点の全 Hom 族の比較への入力。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section
attribute [local irreducible] _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitStrictSpanCocone _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitApexSpan
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpanRootLeg _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpanLeftLeg _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpanRightLeg
variable {A B C D : SSet.{u + 1}} {f : A ⟶ B} {g : A ⟶ C}
  {i : B ⟶ D} {j : C ⟶ D} (hp : IsPushout f g i j) [Mono g] (p : D ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
  (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (f ≫ (i ≫ p))) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c)
  (dB : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (i ≫ p)) (dC : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (j ≫ p))
local notation "q" => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (f ≫ (i ≫ p))
local notation "β" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeNativeRootEdge hp p c hc dB dC
local notation "a" => stdSimplex.δ (1 : Fin 2)
local notation "v" => SSet.yonedaEquiv.symm c
local notation "hv" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightRootExtension_initial_base hp p c hc dB dC
local notation "W" => stdSimplex.δ (1 : Fin 3) ≫
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftRootedTriangle hp p c hc dB dC
local notation "V" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.tetrahedronRootEdge ≫
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRootedRightTetrahedron hp p c hc dB dC
local notation "S" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightRootExtensionSpace hp p c hc dB dC
local notation "hS" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightRootExtensionSpace_isContractibleKan hp p c hc dB dC
local notation "F" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightRootEndpoint hp p c hc dB dC
local notation "L" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpanLeftBoundaryFactor c hc f (i ≫ p) rfl dB
  g (j ≫ p) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePushoutBoundary_eq hp p) dC
local notation "z" => _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone.vertex
  (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitStrictSpanCocone c hc f (i ≫ p) rfl dB
    g (j ≫ p) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePushoutBoundary_eq hp p) dC)
local notation "ε" => Iso.hom (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.pointFunctorEvaluationIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber q z))

local notation "hW" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftRootedTriangle_rootProjection hp p c hc dB dC
local notation "hV" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightCorrectionHomotopy_target_projection hp p c hc dB dC
local notation "hWi" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRootClosingLeft_initial hp p c hc dB dC
local notation "hVi" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightCorrectionHomotopy_target_initial hp p c hc dB dC
local notation "e" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpanRootLeg c hc f (i ≫ p) rfl dB
  g (j ≫ p) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePushoutBoundary_eq hp p) dC

/-- 恒等の類を与えた元の左境界の同じ終点頂点。 -/
def specifiedCoconeRootVerticalEndpointVertex : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber q z) _⦋0⦌ :=
  SSet.HomotopyCategory.objEquiv (Arrow.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map L ε).hom).left

/-- 元の閉じる比較辺と同じ両端を持ち、終点が厳密に恒等となる延長辺。 -/
def specifiedCoconeRootVerticalExtensionEdge :=
  (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.leftFibration_correct_edge_of_identity_arrow F
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRootClosingExtensionEdge hp p c hc dB dC)
    (Arrow.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map L ε).hom).left
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRootClosingExtensionEdge_endpoint_hom_arrow hp p c hc dB dC)).choose

/-- 同じ終点での辺は、指定した頂点の退化一単体そのもの。 -/
lemma specifiedCoconeRootVerticalExtensionEdge_endpoint :
    ((specifiedCoconeRootVerticalExtensionEdge hp p c hc dB dC).map F).edge =
      (SSet.Edge.id (X := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber q z)
        (specifiedCoconeRootVerticalEndpointVertex hp p c hc dB dC)).edge :=
  (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.leftFibration_correct_edge_of_identity_arrow F
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRootClosingExtensionEdge hp p c hc dB dC)
    (Arrow.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map L ε).hom).left
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRootClosingExtensionEdge_endpoint_hom_arrow hp p c hc dB dC)).choose_spec

/-- 同じ左長辺と修正後の右長辺を、全時刻で終点を固定して結ぶ実際の円柱。 -/
def specifiedCoconeRootVerticalHomotopy : SSet.Homotopy W V :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fixedExtensionEdgeHomotopy q β a v hv hW hV hWi hVi
    (specifiedCoconeRootVerticalExtensionEdge hp p c hc dB dC)

/-- 同じ厳密な延長辺を全族として展開した raw な円柱である。 -/
lemma specifiedCoconeRootVerticalHomotopy_raw :
    (specifiedCoconeRootVerticalHomotopy hp p c hc dB dC).h =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry
        (SSet.yonedaEquiv.symm (specifiedCoconeRootVerticalExtensionEdge hp p c hc dB dC).edge ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorExtensionSpaceι q β a v hv) :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fixedExtensionEdgeHomotopy_raw _ _ _ _ _ _ _ _ _ _

/-- 底は元の同じ共通根辺で全時刻に固定する。 -/
lemma specifiedCoconeRootVerticalHomotopy_projection :
    (specifiedCoconeRootVerticalHomotopy hp p c hc dB dC).h ≫ q =
      fst (Δ[1] : SSet.{u + 1}) Δ[1] ≫ β :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fixedExtensionEdgeHomotopy_projection _ _ _ _ _ _ _ _ _ _

/-- 始点は元の同じ共通余錐のまま全時刻に固定する。 -/
lemma specifiedCoconeRootVerticalHomotopy_initial :
    (a ▷ (Δ[1] : SSet.{u + 1})) ≫
        (specifiedCoconeRootVerticalHomotopy hp p c hc dB dC).h =
      fst (Δ[0] : SSet.{u + 1}) Δ[1] ≫ v :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fixedExtensionEdgeHomotopy_initial _ _ _ _ _ _ _ _ _ _

/-- 終点も元の同じ境界頂点で全時刻に固定する。 -/
lemma specifiedCoconeRootVerticalHomotopy_terminal :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (Δ[1] : SSet.{u + 1}) ≫
        (specifiedCoconeRootVerticalHomotopy hp p c hc dB dC).h =
      SSet.const (specifiedCoconeRootVerticalEndpointVertex hp p c hc dB dC).val :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fixedExtensionEdgeHomotopy_endpoint_constant q β a v hv hW hV hWi hVi
    (specifiedCoconeRootVerticalExtensionEdge hp p c hc dB dC) (𝟙 Δ[1]) e (Category.id_comp β)
    (specifiedCoconeRootVerticalEndpointVertex hp p c hc dB dC)
    (specifiedCoconeRootVerticalExtensionEdge_endpoint hp p c hc dB dC)

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
