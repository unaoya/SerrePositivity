module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SpecifiedCocones.SpecifiedCoconeCommonRootEndpoint
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.Homotopies.DiagramComparisons.ContractibleEdgeEvaluation

/-!
概要：左右の実際の三角形比較を、共通根辺の正準比較として保持する。
方針：可縮な延長空間の比較を写し、同じ終点評価の等式で元の類へ接続する。
規約：一意性は延長空間でのみ使う。使われ方：共通空間での境界・付加辺比較の合成。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section
/-- 可換な射の合成に沿う実際の辺は、終点の同じ射の類を与える。 -/
lemma edgeEvaluation_composition_hom_arrow {X Y Z : SSet.{u}}
    (f : X ⟶ Y) (F : Y ⟶ Z) (G : X ⟶ Z) (h : f ≫ F = G)
    {x y : X _⦋0⦌} (s : X.Edge x y) :
    Arrow.mk (SSet.Truncated.HomotopyCategory.homMk ((s.map f).map F).toTruncated) =
      Arrow.mk (SSet.Truncated.HomotopyCategory.homMk (s.map G).toTruncated) := by
  subst G
  rfl

attribute [local irreducible] _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitStrictSpanCocone _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitApexSpan
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpanRootLeg _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpanLeftLeg _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpanRightLeg
variable {A B C D : SSet.{u + 1}} {f : A ⟶ B} {g : A ⟶ C}
  {i : B ⟶ D} {j : C ⟶ D} (hp : IsPushout f g i j) [Mono g] (p : D ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
  (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (f ≫ (i ≫ p))) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c)
  (dB : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (i ≫ p)) (dC : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (j ≫ p))
local notation "S" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightRootExtensionSpace hp p c hc dB dC
local notation "hS" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightRootExtensionSpace_isContractibleKan hp p c hc dB dC
local notation "F" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightRootEndpoint hp p c hc dB dC

/-- 同じ実際の長辺と標準長辺を、共通根辺上の可縮な空間で比較する。 -/
def specifiedCoconeLeftCommonRootComparisonIso :=
  (hS).vertexIso
    ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftCommonRootRestriction hp p c hc dB dC).app _
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftActualTriangleExtensionVertex hp p c hc dB dC))
    ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftCommonRootRestriction hp p c hc dB dC).app _
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftStandardTriangleExtensionVertex hp p c hc dB dC))

/-- 元の三角形の比較は、共通根辺上の同じ二頂点の正準比較へ移る。 -/
lemma specifiedCoconeLeftCommonRootComparisonIso_map :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map
        ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftTriangleExtensionSpace_isContractibleKan
          hp p c hc dB dC).vertexIso
          (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftActualTriangleExtensionVertex hp p c hc dB dC)
          (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftStandardTriangleExtensionVertex hp p c hc dB dC))
        (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftCommonRootRestriction hp p c hc dB dC) =
      specifiedCoconeLeftCommonRootComparisonIso hp p c hc dB dC :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.contractibleVertexIso_map
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftTriangleExtensionSpace_isContractibleKan hp p c hc dB dC)
    hS _ _ _

/-- 正準比較の終点の類は、元の同じ実際の三角形比較辺の終点の類である。 -/
lemma specifiedCoconeLeftCommonRootComparisonIso_endpoint_hom_arrow :
    Arrow.mk ((_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map
      (specifiedCoconeLeftCommonRootComparisonIso hp p c hc dB dC) F).hom) =
      Arrow.mk (SSet.Truncated.HomotopyCategory.homMk
        ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftTriangleComparisonExtensionEdge hp p c hc dB dC).map
          (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftTerminalEvaluation hp p c hc dB dC)).toTruncated) := by
  have h := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.contractibleEdgeEvaluation_hom hS F
    ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftTriangleComparisonExtensionEdge hp p c hc dB dC).map
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftCommonRootRestriction hp p c hc dB dC))
  exact (congrArg Arrow.mk h).symm.trans
    (edgeEvaluation_composition_hom_arrow _ _ _
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftCommonRootRestriction_endpoint hp p c hc dB dC)
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftTriangleComparisonExtensionEdge hp p c hc dB dC))

/-- 共通根辺上の比較の終点も、元の境界自然性と付加輸送の合成の同じ点評価である。 -/
abbrev specifiedCoconeLeftCommonRootComparisonIso_boundary_hom_arrow :=
  (specifiedCoconeLeftCommonRootComparisonIso_endpoint_hom_arrow hp p c hc dB dC).trans
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftTerminalComparison_hom_arrow hp p c hc dB dC)

/-- 同じ実際の長辺と標準長辺を、共通根辺上の可縮な空間で比較する。 -/
def specifiedCoconeRightPrefixCommonRootComparisonIso :=
  (hS).vertexIso
    ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightPrefixCommonRootRestriction hp p c hc dB dC).app _
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightPrefixActualTriangleExtensionVertex hp p c hc dB dC))
    ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightPrefixCommonRootRestriction hp p c hc dB dC).app _
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightPrefixStandardTriangleExtensionVertex hp p c hc dB dC))

/-- 元の三角形の比較は、共通根辺上の同じ二頂点の正準比較へ移る。 -/
lemma specifiedCoconeRightPrefixCommonRootComparisonIso_map :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map
        ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightPrefixTriangleExtensionSpace_isContractibleKan
          hp p c hc dB dC).vertexIso
          (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightPrefixActualTriangleExtensionVertex hp p c hc dB dC)
          (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightPrefixStandardTriangleExtensionVertex hp p c hc dB dC))
        (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightPrefixCommonRootRestriction hp p c hc dB dC) =
      specifiedCoconeRightPrefixCommonRootComparisonIso hp p c hc dB dC :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.contractibleVertexIso_map
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightPrefixTriangleExtensionSpace_isContractibleKan hp p c hc dB dC)
    hS _ _ _

/-- 正準比較の終点の類は、元の同じ実際の三角形比較辺の終点の類である。 -/
lemma specifiedCoconeRightPrefixCommonRootComparisonIso_endpoint_hom_arrow :
    Arrow.mk ((_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map
      (specifiedCoconeRightPrefixCommonRootComparisonIso hp p c hc dB dC) F).hom) =
      Arrow.mk (SSet.Truncated.HomotopyCategory.homMk
        ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightPrefixTriangleComparisonExtensionEdge hp p c hc dB dC).map
          (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightPrefixTerminalEvaluation hp p c hc dB dC)).toTruncated) := by
  have h := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.contractibleEdgeEvaluation_hom hS F
    ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightPrefixTriangleComparisonExtensionEdge hp p c hc dB dC).map
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightPrefixCommonRootRestriction hp p c hc dB dC))
  exact (congrArg Arrow.mk h).symm.trans
    (edgeEvaluation_composition_hom_arrow _ _ _
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightPrefixCommonRootRestriction_endpoint hp p c hc dB dC)
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightPrefixTriangleComparisonExtensionEdge hp p c hc dB dC))

/-- 共通根辺上の比較の終点も、元の境界自然性と付加輸送の合成の同じ点評価である。 -/
abbrev specifiedCoconeRightPrefixCommonRootComparisonIso_boundary_hom_arrow :=
  (specifiedCoconeRightPrefixCommonRootComparisonIso_endpoint_hom_arrow hp p c hc dB dC).trans
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightPrefixTerminalComparison_hom_arrow hp p c hc dB dC)

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
