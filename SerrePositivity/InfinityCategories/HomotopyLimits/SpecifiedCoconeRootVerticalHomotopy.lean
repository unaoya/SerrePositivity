module

public import SerrePositivity.InfinityCategories.HomotopyLimits.SpecifiedCoconeRootClosingHomotopy
public import SerrePositivity.InfinityCategories.HomotopyLimits.PointTransportEndpointFibration
public import SerrePositivity.InfinityCategories.HomotopyLimits.NullEndpointEdge
public import SerrePositivity.InfinityCategories.HomotopyLimits.FixedExtensionEdgeHomotopy

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
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section
attribute [local irreducible] partialColimitStrictSpanCocone partialColimitApexSpan
  partialColimitSpanRootLeg partialColimitSpanLeftLeg partialColimitSpanRightLeg
variable {A B C D : SSet.{u + 1}} {f : A ⟶ B} {g : A ⟶ C}
  {i : B ⟶ D} {j : C ⟶ D} (hp : IsPushout f g i j) [Mono g] (p : D ⟶ SpaceInfinity.{u})
  (c : JoinCocone (f ≫ (i ≫ p))) (hc : IsColimitCone c)
  (dB : JoinCocone (i ≫ p)) (dC : JoinCocone (j ≫ p))
local notation "q" => sliceUnderProjection (f ≫ (i ≫ p))
local notation "β" => specifiedCoconeNativeRootEdge hp p c hc dB dC
local notation "a" => stdSimplex.δ (1 : Fin 2)
local notation "v" => SSet.yonedaEquiv.symm c
local notation "hv" => specifiedCoconeRightRootExtension_initial_base hp p c hc dB dC
local notation "W" => stdSimplex.δ (1 : Fin 3) ≫
  specifiedCoconeLeftRootedTriangle hp p c hc dB dC
local notation "V" => tetrahedronRootEdge ≫
  specifiedCoconeRootedRightTetrahedron hp p c hc dB dC
local notation "S" => specifiedCoconeRightRootExtensionSpace hp p c hc dB dC
local notation "hS" => specifiedCoconeRightRootExtensionSpace_isContractibleKan hp p c hc dB dC
local notation "F" => specifiedCoconeRightRootEndpoint hp p c hc dB dC
local notation "L" => partialColimitSpanLeftBoundaryFactor c hc f (i ≫ p) rfl dB
  g (j ≫ p) (coconePushoutBoundary_eq hp p) dC
local notation "z" => JoinCocone.vertex
  (partialColimitStrictSpanCocone c hc f (i ≫ p) rfl dB
    g (j ≫ p) (coconePushoutBoundary_eq hp p) dC)
local notation "ε" => Iso.hom (pointFunctorEvaluationIso (vertexFiber q z))

local notation "hW" => specifiedCoconeLeftRootedTriangle_rootProjection hp p c hc dB dC
local notation "hV" => specifiedCoconeRightCorrectionHomotopy_target_projection hp p c hc dB dC
local notation "hWi" => specifiedCoconeRootClosingLeft_initial hp p c hc dB dC
local notation "hVi" => specifiedCoconeRightCorrectionHomotopy_target_initial hp p c hc dB dC
local notation "e" => partialColimitSpanRootLeg c hc f (i ≫ p) rfl dB
  g (j ≫ p) (coconePushoutBoundary_eq hp p) dC

/-- 恒等の類を与えた元の左境界の同じ終点頂点。 -/
def specifiedCoconeRootVerticalEndpointVertex : (vertexFiber q z) _⦋0⦌ :=
  SSet.HomotopyCategory.objEquiv (Arrow.mk (VertexIso.map L ε).hom).left

/-- 元の閉じる比較辺と同じ両端を持ち、終点が厳密に恒等となる延長辺。 -/
def specifiedCoconeRootVerticalExtensionEdge :=
  (leftFibration_correct_edge_of_identity_arrow F
    (specifiedCoconeRootClosingExtensionEdge hp p c hc dB dC)
    (Arrow.mk (VertexIso.map L ε).hom).left
    (specifiedCoconeRootClosingExtensionEdge_endpoint_hom_arrow hp p c hc dB dC)).choose

/-- 同じ終点での辺は、指定した頂点の退化一単体そのもの。 -/
lemma specifiedCoconeRootVerticalExtensionEdge_endpoint :
    ((specifiedCoconeRootVerticalExtensionEdge hp p c hc dB dC).map F).edge =
      (SSet.Edge.id (X := vertexFiber q z)
        (specifiedCoconeRootVerticalEndpointVertex hp p c hc dB dC)).edge :=
  (leftFibration_correct_edge_of_identity_arrow F
    (specifiedCoconeRootClosingExtensionEdge hp p c hc dB dC)
    (Arrow.mk (VertexIso.map L ε).hom).left
    (specifiedCoconeRootClosingExtensionEdge_endpoint_hom_arrow hp p c hc dB dC)).choose_spec

/-- 同じ左長辺と修正後の右長辺を、全時刻で終点を固定して結ぶ実際の円柱。 -/
def specifiedCoconeRootVerticalHomotopy : SSet.Homotopy W V :=
  fixedExtensionEdgeHomotopy q β a v hv hW hV hWi hVi
    (specifiedCoconeRootVerticalExtensionEdge hp p c hc dB dC)

/-- 同じ厳密な延長辺を全族として展開した raw な円柱である。 -/
lemma specifiedCoconeRootVerticalHomotopy_raw :
    (specifiedCoconeRootVerticalHomotopy hp p c hc dB dC).h =
      relativeFunctorUncurry
        (SSet.yonedaEquiv.symm (specifiedCoconeRootVerticalExtensionEdge hp p c hc dB dC).edge ≫
          relativeFunctorExtensionSpaceι q β a v hv) :=
  fixedExtensionEdgeHomotopy_raw _ _ _ _ _ _ _ _ _ _

/-- 底は元の同じ共通根辺で全時刻に固定する。 -/
lemma specifiedCoconeRootVerticalHomotopy_projection :
    (specifiedCoconeRootVerticalHomotopy hp p c hc dB dC).h ≫ q =
      fst (Δ[1] : SSet.{u + 1}) Δ[1] ≫ β :=
  fixedExtensionEdgeHomotopy_projection _ _ _ _ _ _ _ _ _ _

/-- 始点は元の同じ共通余錐のまま全時刻に固定する。 -/
lemma specifiedCoconeRootVerticalHomotopy_initial :
    (a ▷ (Δ[1] : SSet.{u + 1})) ≫
        (specifiedCoconeRootVerticalHomotopy hp p c hc dB dC).h =
      fst (Δ[0] : SSet.{u + 1}) Δ[1] ≫ v :=
  fixedExtensionEdgeHomotopy_initial _ _ _ _ _ _ _ _ _ _

/-- 終点も元の同じ境界頂点で全時刻に固定する。 -/
lemma specifiedCoconeRootVerticalHomotopy_terminal :
    prismEndpoint 1 (Δ[1] : SSet.{u + 1}) ≫
        (specifiedCoconeRootVerticalHomotopy hp p c hc dB dC).h =
      SSet.const (specifiedCoconeRootVerticalEndpointVertex hp p c hc dB dC).val :=
  fixedExtensionEdgeHomotopy_endpoint_constant q β a v hv hW hV hWi hVi
    (specifiedCoconeRootVerticalExtensionEdge hp p c hc dB dC) (𝟙 Δ[1]) e (Category.id_comp β)
    (specifiedCoconeRootVerticalEndpointVertex hp p c hc dB dC)
    (specifiedCoconeRootVerticalExtensionEdge_endpoint hp p c hc dB dC)

end
end SerrePositivity.InfinityCategories.HomotopyLimits
