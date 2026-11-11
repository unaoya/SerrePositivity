module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.PointTransportExtension
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.HomotopyComponentEvaluation

/-!
概要：根辺の点比較の終点を、元の二単体による合成同型の同じ成分へ同定する。
方針：点円柱の終点と全族の合成ホモトピーの点評価の raw な射を照合する。
規約：辺の類を選び直さない。使われ方：左右の標準長辺間の native な比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section

private lemma prismPointCylinder_endpoint_shape {A : SSet.{u}} (v : A _⦋0⦌) :
    lift (SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) (𝟙 (Δ[1] : SSet.{u})) ≫
        ((lift (𝟙 Δ[1]) (SSet.const v)) ▷ (Δ[1] : SSet.{u})) =
      lift (SSet.const v) (𝟙 (Δ[1] : SSet.{u})) ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 A ▷ (Δ[1] : SSet.{u})) := by
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint, lift_whiskerRight, comp_lift, Category.comp_id, SSet.comp_const]

variable {E B : SSet.{u}} (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p]
  {a b c : B _⦋0⦌} {e : B.Edge a b} {f : B.Edge b c} {g : B.Edge a c}
  (v : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p a) _⦋0⦌) (σ : SSet.Edge.CompStruct e f g)
local notation "β" => SSet.yonedaEquiv.symm g.edge
local notation "i" => stdSimplex.δ (1 : Fin 2)
local notation "w" => SSet.yonedaEquiv.symm v.val
local notation "hv" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pointTransportExtension_initial_base p g v
local notation "H" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentTransportPointComparisonHomotopy p σ v
local notation "s" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentTransportPointComparisonExtensionEdge p v σ
local notation "F" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pointTransportExtensionEndpoint p g v
local notation "M" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentTransportTriangleCompositionHomotopy p σ
local notation "I" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentTransportTriangleCompositionIso p σ

/-- 同じ点比較辺の終点は、元の全族の合成円柱の同じ頂点での評価。 -/
lemma coherentTransportPointComparisonExtensionEdge_endpoint_projection :
    SSet.yonedaEquiv.symm ((s).map F).edge ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p c =
      lift (SSet.const v) (𝟙 (Δ[1] : SSet.{u})) ≫ (M).h ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p c := by
  have h := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fixedExtensionEdgeTarget_map_homotopy_raw p β i w hv (𝟙 Δ[1]) g
    (Category.id_comp β)
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentTransportLongPoint_projection p v σ) (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.standardTransportPoint_projection p g v)
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentTransportLongPoint_initial p v σ) (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.standardTransportPoint_initial p g v)
    H (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentTransportPointComparisonHomotopy_projection p σ v)
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentTransportPointComparisonHomotopy_initial_face p v σ)
  change SSet.yonedaEquiv.symm ((s).map F).edge ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p c = _ at h
  refine h.trans ?_
  change lift (SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2)))
    (𝟙 (Δ[1] : SSet.{u})) ≫ (H).h = _
  rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentTransportPointComparisonHomotopy_raw,
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentTransportTriangleCompositionHomotopy_projection, ← Category.assoc,
    prismPointCylinder_endpoint_shape, Category.assoc]

/-- 元の二単体の同じ合成同型の成分が、点比較辺の終点の類を与える。 -/
lemma coherentTransportPointComparisonExtensionEdge_endpoint_hom_arrow :
    Arrow.mk (SSet.Truncated.HomotopyCategory.homMk ((s).map F).toTruncated) =
      Arrow.mk ((I).toNatIso.hom.app (SSet.HomotopyCategory.mk v)) := by
  apply _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.functorHomotopy_component_hom_arrow M I rfl v ((s).map F)
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext p c
  exact coherentTransportPointComparisonExtensionEdge_endpoint_projection p v σ

/-- 同じ根辺の正準比較の終点の類も、元の二単体の合成同型の同じ成分である。 -/
abbrev coherentTransportPointCanonicalComparison_endpoint_hom_arrow :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.contractibleEdgeEvaluation_hom_arrow
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pointTransportExtensionSpace_isContractibleKan p g v) F (s)
    ((I).toNatIso.hom.app (SSet.HomotopyCategory.mk v))
    (coherentTransportPointComparisonExtensionEdge_endpoint_hom_arrow p v σ)

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
