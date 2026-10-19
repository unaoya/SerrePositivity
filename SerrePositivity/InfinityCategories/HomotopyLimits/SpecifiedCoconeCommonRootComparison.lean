module

public import SerrePositivity.InfinityCategories.HomotopyLimits.SpecifiedCoconeCommonRootEndpoint
public import SerrePositivity.InfinityCategories.HomotopyLimits.ContractibleEdgeEvaluation

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
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section
/-- 可換な射の合成に沿う実際の辺は、終点の同じ射の類を与える。 -/
lemma edgeEvaluation_composition_hom_arrow {X Y Z : SSet.{u}}
    (f : X ⟶ Y) (F : Y ⟶ Z) (G : X ⟶ Z) (h : f ≫ F = G)
    {x y : X _⦋0⦌} (s : X.Edge x y) :
    Arrow.mk (SSet.Truncated.HomotopyCategory.homMk ((s.map f).map F).toTruncated) =
      Arrow.mk (SSet.Truncated.HomotopyCategory.homMk (s.map G).toTruncated) := by
  subst G
  rfl

attribute [local irreducible] partialColimitStrictSpanCocone partialColimitApexSpan
  partialColimitSpanRootLeg partialColimitSpanLeftLeg partialColimitSpanRightLeg
variable {A B C D : SSet.{u + 1}} {f : A ⟶ B} {g : A ⟶ C}
  {i : B ⟶ D} {j : C ⟶ D} (hp : IsPushout f g i j) [Mono g] (p : D ⟶ SpaceInfinity.{u})
  (c : JoinCocone (f ≫ (i ≫ p))) (hc : IsColimitCone c)
  (dB : JoinCocone (i ≫ p)) (dC : JoinCocone (j ≫ p))
local notation "S" => specifiedCoconeRightRootExtensionSpace hp p c hc dB dC
local notation "hS" => specifiedCoconeRightRootExtensionSpace_isContractibleKan hp p c hc dB dC
local notation "F" => specifiedCoconeRightRootEndpoint hp p c hc dB dC

/-- 同じ実際の長辺と標準長辺を、共通根辺上の可縮な空間で比較する。 -/
def specifiedCoconeLeftCommonRootComparisonIso :=
  (hS).vertexIso
    ((specifiedCoconeLeftCommonRootRestriction hp p c hc dB dC).app _
      (specifiedCoconeLeftActualTriangleExtensionVertex hp p c hc dB dC))
    ((specifiedCoconeLeftCommonRootRestriction hp p c hc dB dC).app _
      (specifiedCoconeLeftStandardTriangleExtensionVertex hp p c hc dB dC))

/-- 元の三角形の比較は、共通根辺上の同じ二頂点の正準比較へ移る。 -/
lemma specifiedCoconeLeftCommonRootComparisonIso_map :
    VertexIso.map
        ((specifiedCoconeLeftTriangleExtensionSpace_isContractibleKan
          hp p c hc dB dC).vertexIso
          (specifiedCoconeLeftActualTriangleExtensionVertex hp p c hc dB dC)
          (specifiedCoconeLeftStandardTriangleExtensionVertex hp p c hc dB dC))
        (specifiedCoconeLeftCommonRootRestriction hp p c hc dB dC) =
      specifiedCoconeLeftCommonRootComparisonIso hp p c hc dB dC :=
  contractibleVertexIso_map
    (specifiedCoconeLeftTriangleExtensionSpace_isContractibleKan hp p c hc dB dC)
    hS _ _ _

/-- 正準比較の終点の類は、元の同じ実際の三角形比較辺の終点の類である。 -/
lemma specifiedCoconeLeftCommonRootComparisonIso_endpoint_hom_arrow :
    Arrow.mk ((VertexIso.map
      (specifiedCoconeLeftCommonRootComparisonIso hp p c hc dB dC) F).hom) =
      Arrow.mk (SSet.Truncated.HomotopyCategory.homMk
        ((specifiedCoconeLeftTriangleComparisonExtensionEdge hp p c hc dB dC).map
          (specifiedCoconeLeftTerminalEvaluation hp p c hc dB dC)).toTruncated) := by
  have h := contractibleEdgeEvaluation_hom hS F
    ((specifiedCoconeLeftTriangleComparisonExtensionEdge hp p c hc dB dC).map
      (specifiedCoconeLeftCommonRootRestriction hp p c hc dB dC))
  exact (congrArg Arrow.mk h).symm.trans
    (edgeEvaluation_composition_hom_arrow _ _ _
      (specifiedCoconeLeftCommonRootRestriction_endpoint hp p c hc dB dC)
      (specifiedCoconeLeftTriangleComparisonExtensionEdge hp p c hc dB dC))

/-- 共通根辺上の比較の終点も、元の境界自然性と付加輸送の合成の同じ点評価である。 -/
abbrev specifiedCoconeLeftCommonRootComparisonIso_boundary_hom_arrow :=
  (specifiedCoconeLeftCommonRootComparisonIso_endpoint_hom_arrow hp p c hc dB dC).trans
    (specifiedCoconeLeftTerminalComparison_hom_arrow hp p c hc dB dC)

/-- 同じ実際の長辺と標準長辺を、共通根辺上の可縮な空間で比較する。 -/
def specifiedCoconeRightPrefixCommonRootComparisonIso :=
  (hS).vertexIso
    ((specifiedCoconeRightPrefixCommonRootRestriction hp p c hc dB dC).app _
      (specifiedCoconeRightPrefixActualTriangleExtensionVertex hp p c hc dB dC))
    ((specifiedCoconeRightPrefixCommonRootRestriction hp p c hc dB dC).app _
      (specifiedCoconeRightPrefixStandardTriangleExtensionVertex hp p c hc dB dC))

/-- 元の三角形の比較は、共通根辺上の同じ二頂点の正準比較へ移る。 -/
lemma specifiedCoconeRightPrefixCommonRootComparisonIso_map :
    VertexIso.map
        ((specifiedCoconeRightPrefixTriangleExtensionSpace_isContractibleKan
          hp p c hc dB dC).vertexIso
          (specifiedCoconeRightPrefixActualTriangleExtensionVertex hp p c hc dB dC)
          (specifiedCoconeRightPrefixStandardTriangleExtensionVertex hp p c hc dB dC))
        (specifiedCoconeRightPrefixCommonRootRestriction hp p c hc dB dC) =
      specifiedCoconeRightPrefixCommonRootComparisonIso hp p c hc dB dC :=
  contractibleVertexIso_map
    (specifiedCoconeRightPrefixTriangleExtensionSpace_isContractibleKan hp p c hc dB dC)
    hS _ _ _

/-- 正準比較の終点の類は、元の同じ実際の三角形比較辺の終点の類である。 -/
lemma specifiedCoconeRightPrefixCommonRootComparisonIso_endpoint_hom_arrow :
    Arrow.mk ((VertexIso.map
      (specifiedCoconeRightPrefixCommonRootComparisonIso hp p c hc dB dC) F).hom) =
      Arrow.mk (SSet.Truncated.HomotopyCategory.homMk
        ((specifiedCoconeRightPrefixTriangleComparisonExtensionEdge hp p c hc dB dC).map
          (specifiedCoconeRightPrefixTerminalEvaluation hp p c hc dB dC)).toTruncated) := by
  have h := contractibleEdgeEvaluation_hom hS F
    ((specifiedCoconeRightPrefixTriangleComparisonExtensionEdge hp p c hc dB dC).map
      (specifiedCoconeRightPrefixCommonRootRestriction hp p c hc dB dC))
  exact (congrArg Arrow.mk h).symm.trans
    (edgeEvaluation_composition_hom_arrow _ _ _
      (specifiedCoconeRightPrefixCommonRootRestriction_endpoint hp p c hc dB dC)
      (specifiedCoconeRightPrefixTriangleComparisonExtensionEdge hp p c hc dB dC))

/-- 共通根辺上の比較の終点も、元の境界自然性と付加輸送の合成の同じ点評価である。 -/
abbrev specifiedCoconeRightPrefixCommonRootComparisonIso_boundary_hom_arrow :=
  (specifiedCoconeRightPrefixCommonRootComparisonIso_endpoint_hom_arrow hp p c hc dB dC).trans
    (specifiedCoconeRightPrefixTerminalComparison_hom_arrow hp p c hc dB dC)

end
end SerrePositivity.InfinityCategories.HomotopyLimits
