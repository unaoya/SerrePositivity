module

public import
  SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SpecifiedCocones.SpecifiedCoconeCommonRootRestriction
public import
  SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.KanExtensions.FixedExtensionEdgeEvaluationNaturality
public import
  SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SpecifiedCocones.SpecifiedCoconeRightCorrectionEndpoint
public import
  SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SpecifiedCocones.SpecifiedCoconeLeftTerminalComposition
public import
  SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SpecifiedCocones.SpecifiedCoconeRightPrefixTerminalComposition

/-!
概要：共通長辺へ移した左右の比較を、元の三角形と同じ終点で評価する。
方針：底の移送・長辺制限・終端辺の終点の厳密な一致を合成する。
規約：実際の比較辺の一単体を保持する。使われ方：元の境界自然性の共通空間への接続。
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
local notation "v" => SSet.yonedaEquiv.symm c
local notation "k" => stdSimplex.δ (1 : Fin 3)
local notation "a" => stdSimplex.δ (1 : Fin 2)
local notation "σL" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpanLeftTriangle c hc f (i ≫ p) rfl dB
  g (j ≫ p) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePushoutBoundary_eq hp p) dC
local notation "σR" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpanRightTriangle c hc f (i ≫ p) rfl dB
  g (j ≫ p) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePushoutBoundary_eq hp p) dC
local notation "βL" => SSet.yonedaEquiv.symm (SSet.Edge.CompStruct.simplex σL)
local notation "βR" => SSet.yonedaEquiv.symm (SSet.Edge.CompStruct.simplex σR)
local notation "hvL" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftTriangleExtension_initial_base hp p c hc dB dC
local notation "hvR" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightPrefixTriangleExtension_initial_base hp p c hc dB dC
local notation "hv" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightRootExtension_initial_base hp p c hc dB dC
local notation "L" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftRootedTriangle hp p c hc dB dC
local notation "R" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightPrefixRootedTriangle hp p c hc dB dC
local notation "S" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightRootExtensionSpace hp p c hc dB dC

local notation "e" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpanRootLeg c hc f (i ≫ p) rfl dB
  g (j ≫ p) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePushoutBoundary_eq hp p) dC
local notation "eL" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpanLeftLeg c hc f (i ≫ p) rfl dB
  g (j ≫ p) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePushoutBoundary_eq hp p) dC
local notation "eR" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpanRightLeg c hc f (i ≫ p) rfl dB
  g (j ≫ p) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePushoutBoundary_eq hp p) dC
local notation "k₀" => stdSimplex.δ (0 : Fin 3)
local notation "F" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightRootEndpoint hp p c hc dB dC

/-- 共通根辺へ移してからの終点評価は、元の左三角形の終点評価そのもの。 -/
lemma specifiedCoconeLeftCommonRootRestriction_endpoint :
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftCommonRootRestriction hp p c hc dB dC ≫ F =
      _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftTerminalEvaluation hp p c hc dB dC := by
  dsimp only [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftCommonRootRestriction, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightRootEndpoint]
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fixedExtensionBaseIso_edgeTarget q
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftTriangleLongBase hp p c hc dB dC) a v
    ((hvL).trans (Category.assoc _ _ _)) hv (𝟙 Δ[1]) e
    ((Category.id_comp _).trans
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftTriangleLongBase hp p c hc dB dC)) (Category.id_comp β)]
  dsimp only [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftTriangleLongRestriction]
  rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fixedExtensionRestriction_edgeTarget]
  exact _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fixedExtensionEdgeTarget_eq_of_vertex q βL (a ≫ k) v hvL
    ((𝟙 Δ[1]) ≫ k) k₀ e eL _
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftTerminalEdge_base hp p c hc dB dC) (by decide)

/-- 元の実際の比較辺を共通根辺へ移しても、終点の同じ一単体を回収する。 -/
lemma specifiedCoconeLeftCommonRootRestriction_endpoint_edge
    {x y : (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftTriangleExtensionSpace hp p c hc dB dC) _⦋0⦌}
    (s : (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftTriangleExtensionSpace hp p c hc dB dC).Edge x y) :
    ((s.map (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftCommonRootRestriction hp p c hc dB dC)).map F).edge =
      (s.map (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftTerminalEvaluation hp p c hc dB dC)).edge :=
  congrArg (fun z ↦ z.app _ s.edge)
    (specifiedCoconeLeftCommonRootRestriction_endpoint hp p c hc dB dC)

/-- 共通根辺へ移してからの終点評価は、元の右初面三角形の終点評価そのもの。 -/
lemma specifiedCoconeRightPrefixCommonRootRestriction_endpoint :
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightPrefixCommonRootRestriction hp p c hc dB dC ≫ F =
      _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightPrefixTerminalEvaluation hp p c hc dB dC := by
  dsimp only [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightPrefixCommonRootRestriction, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightRootEndpoint]
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fixedExtensionBaseIso_edgeTarget q
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightPrefixTriangleLongBase hp p c hc dB dC) a v
    ((hvR).trans (Category.assoc _ _ _)) hv (𝟙 Δ[1]) e
    ((Category.id_comp _).trans
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightPrefixTriangleLongBase hp p c hc dB dC)) (Category.id_comp β)]
  dsimp only [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightPrefixTriangleLongRestriction]
  rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fixedExtensionRestriction_edgeTarget]
  exact _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fixedExtensionEdgeTarget_eq_of_vertex q βR (a ≫ k) v hvR
    ((𝟙 Δ[1]) ≫ k) k₀ e eR _
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightPrefixTerminalEdge_base hp p c hc dB dC) (by decide)

/-- 元の実際の比較辺を共通根辺へ移しても、終点の同じ一単体を回収する。 -/
lemma specifiedCoconeRightPrefixCommonRootRestriction_endpoint_edge
    {x y : (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightPrefixTriangleExtensionSpace hp p c hc dB dC) _⦋0⦌}
    (s : (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightPrefixTriangleExtensionSpace hp p c hc dB dC).Edge x y) :
    ((s.map (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightPrefixCommonRootRestriction hp p c hc dB dC)).map F).edge =
      (s.map (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightPrefixTerminalEvaluation hp p c hc dB dC)).edge :=
  congrArg (fun z ↦ z.app _ s.edge)
    (specifiedCoconeRightPrefixCommonRootRestriction_endpoint hp p c hc dB dC)

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
