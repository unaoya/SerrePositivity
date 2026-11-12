module

public import SerrePositivity.KST.LocalizingInvariants.SpectrumTriangleCommutation
public import SerrePositivity.KST.LocalizingInvariants.FiberDiagramNativeRightPath
public import SerrePositivity.KST.LocalizingInvariants.FiberDiagramRightDecomposition

/-!
概要：元の fiber 比較の上下三角形に、BF 区間を保持する二つの可換式を適用する。
方針：元の六辺を使い、対角分解の全射を同じ元の二単体に同定する。
規約：右辺の h Sp 可換性だけに落とさない。使われ方：全 h Fun の右辺比較の貼合せ。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.LocalizingInvariants.FiberDiagram

local instance nativeTriangleCommutationCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory

variable {D E : FiberDiagram.{u}} (f : D ⟶ E)

def nativeRightLowerPost := SpectrumTriangleNormalization.sourcePost
  (NativeFiber.rightMap D.triangle) (rightLower f)
  ((rightLower_two f).trans (rightMap_edge D).symm)
  (rightDiagonalMap f) ((rightLower_one f).trans (rightDiagonalMap_edge f).symm)

def nativeRightUpperPre := SpectrumTriangleNormalization.sourcePre
  (NativeFiber.rightMap E.triangle) (rightUpper f)
  ((rightUpper_zero f).trans (rightMap_edge E).symm)
  (rightDiagonalMap f) ((rightUpper_one f).trans (rightDiagonalMap_edge f).symm)

def nativeRightCanonicalPost := SpectrumTriangleNormalization.canonicalPost
  (NativeFiber.rightMap D.triangle) (comparisonMap f 1 1)

def nativeRightCanonicalPre := SpectrumTriangleNormalization.canonicalPre
  (comparisonMap f 1 0) (NativeFiber.rightMap E.triangle)

lemma nativeRightLowerPost_comp :
    Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (nativeRightLowerPost f)) ≫
      SpectrumMappingPath.arrowHom (nativeRightLowerRealization f).path =
    Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (nativeRightCanonicalPost f)) :=
  SpectrumTriangleNormalization.post_commutation _ _ _ _ _ _ _

lemma nativeRightUpperPre_eq :
    Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (nativeRightUpperPre f)) =
    SpectrumMappingPath.arrowHom (nativeRightUpperRealization f).path ≫
      Truncated.HomotopyCategory.homMk
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (nativeRightCanonicalPre f)) :=
  SpectrumTriangleNormalization.pre_commutation _ _ _ _ _ _ _

lemma rightAfterBottom_native :
    Arrow.mk (Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (rightAfterBottom f))) =
    Arrow.mk (Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (nativeRightLowerPost f))) := by
  apply HomotopyArrow.congr
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 1 ≫ (rightComparisonHomotopy f).h =
      SSet.yonedaEquiv.symm (rightLower f) := by
    simpa only [Equiv.symm_apply_apply] using
      congrArg SSet.yonedaEquiv.symm (rightLower_triangle f)
  change SquareDiagonal.postShape ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 1 ≫ (rightComparisonHomotopy f).h = _
  rw [he]
  rfl

lemma rightBeforeTop_native :
    Arrow.mk (Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (rightBeforeTop f))) =
    Arrow.mk (Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (nativeRightUpperPre f))) := by
  apply HomotopyArrow.congr
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 0 ≫ (rightComparisonHomotopy f).h =
      SSet.yonedaEquiv.symm (rightUpper f) := by
    simpa only [Equiv.symm_apply_apply] using
      congrArg SSet.yonedaEquiv.symm (rightUpper_triangle f)
  change SquareDiagonal.preShape ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 0 ≫ (rightComparisonHomotopy f).h = _
  rw [he]
  rfl

end SerrePositivity.KST.LocalizingInvariants.FiberDiagram
