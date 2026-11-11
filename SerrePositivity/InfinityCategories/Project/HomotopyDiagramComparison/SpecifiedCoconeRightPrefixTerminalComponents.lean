module

public import
  SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SpecifiedCoconeRightPrefixTerminalPoint
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.MapTransportPrismComparison
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoconeBoundaryTransportCylinder

/-!
概要：右初面三角形の全終端辺の輸送比較の二成分を、元の境界自然性と恒等射へ同定する。
方針：実際の二つの点 prism を回収し、同じ全族の同型の成分公式へ渡す。
規約：端点の表示変更は Arrow で明示する。使われ方：右初面終点比較の合成式。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section
variable {A B C D : SSet.{u + 1}} {f : A ⟶ B} {g : A ⟶ C}
  {i : B ⟶ D} {j : C ⟶ D} (hp : IsPushout f g i j) [Mono g] (p : D ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
  (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (f ≫ (i ≫ p))) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c)
  (dB : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (i ≫ p)) (dC : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (j ≫ p))
local notation "q" => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (f ≫ (i ≫ p))
local notation "qC" => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (j ≫ p)
local notation "e" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpanRightLeg c hc f (i ≫ p) rfl dB
  g (j ≫ p) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePushoutBoundary_eq hp p) dC
local notation "z" => _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone.vertex
  (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitStrictSpanCocone c hc f (i ≫ p) rfl dB
    g (j ≫ p) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePushoutBoundary_eq hp p) dC)
local notation "H" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightPrefixTerminalPrism hp p c hc dB dC
local notation "F" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightPrefixMiddleEvaluation hp p c hc dB dC
local notation "G" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightPrefixTerminalEvaluation hp p c hc dB dC
local notation "x" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightPrefixActualTriangleExtensionVertex hp p c hc dB dC
local notation "y" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightPrefixStandardTriangleExtensionVertex hp p c hc dB dC
local notation "vC" => _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.initialFiberVertexAt qC dC (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone.vertex dC) rfl
local notation "r" => _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedCoconeRestriction (j ≫ p) g (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePushoutBoundary_eq hp p)
local notation "hr" => _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedCoconeRestriction_projection (j ≫ p) g (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePushoutBoundary_eq
  hp p)
local notation "he" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightPrefixTerminalEdge_base hp p c hc dB dC

/-- 実際の三角形の点 prism は、同じ標準 prism の制限自然性に使う入力そのもの。 -/
lemma specifiedCoconeRightPrefixTerminalPrism_actual_map :
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.prismParameterPrecomp H (SSet.yonedaEquiv.symm x) =
      _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.prismParameterPrecomp (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.mapTransportPrism qC r e) (SSet.yonedaEquiv.symm vC) := by
  refine (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightPrefixTerminalPrism_actual_point hp p c hc dB dC).trans ?_
  refine Eq.trans ?_ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.prismParameterPrecomp_point (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.mapTransportPrism qC r e) vC).symm
  simp only [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.mapTransportPrism, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.prismVertexEvaluation, Category.assoc]

/-- 実際の三角形成分は、元の指定境界路の制限自然性同型を点評価した射。 -/
abbrev specifiedCoconeRightPrefixTerminalTransport_actual_hom_arrow :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.prismTransportComponent_map_pointIso_hom_arrow qC q r hr e F G H
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fixedExtensionEdgeSource_ι _ _ _ _ _ _ _ he).symm
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fixedExtensionEdgeTarget_ι _ _ _ _ _ _ _ he).symm
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fixedExtensionEdgePrism_projection _ _ _ _ _ _ _ he)
    x vC (specifiedCoconeRightPrefixTerminalPrism_actual_map hp p c hc dB dC)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeBoundaryTransportPointIso g (j ≫ p) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePushoutBoundary_eq hp p) dC e)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeBoundaryTransportPointIso_hom_arrow g (j ≫ p) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePushoutBoundary_eq hp p) dC e)

local notation "v₀" => _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.initialFiberVertexAt q c (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone.vertex c) rfl
local notation "e₀" => SSet.Edge.ofTruncated (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitAttachmentApexEdge c hc g (j ≫ p)
  (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePushoutBoundary_eq hp p) dC)
local notation "v₁" => NatTrans.app (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.edgeTransport q e₀) (Opposite.op ⦋0⦌) v₀

/-- 標準三角形の点 prism は、同じ第一輸送後の点を始点とする標準 prism。 -/
lemma specifiedCoconeRightPrefixTerminalPrism_standard_map :
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.prismParameterPrecomp H (SSet.yonedaEquiv.symm y) =
      _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.prismTransportStandard q e (SSet.yonedaEquiv.symm v₁) := by
  exact (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightPrefixTerminalPrism_standard_point hp p c hc dB dC).trans
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.prismParameterPrecomp_point (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.transportEdgePrism q e) v₁).symm

/-- 標準側の成分公式。同じ標準 prism の定値比較円柱から恒等射を得る。 -/
abbrev specifiedCoconeRightPrefixTerminalTransport_standard_hom_arrow :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.prismTransportComponent_standard_hom_arrow q e F G H
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fixedExtensionEdgeSource_ι _ _ _ _ _ _ _ he).symm
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fixedExtensionEdgeTarget_ι _ _ _ _ _ _ _ he).symm
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fixedExtensionEdgePrism_projection _ _ _ _ _ _ _ he)
    y (SSet.yonedaEquiv.symm v₁)
    (specifiedCoconeRightPrefixTerminalPrism_standard_map hp p c hc dB dC)

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
