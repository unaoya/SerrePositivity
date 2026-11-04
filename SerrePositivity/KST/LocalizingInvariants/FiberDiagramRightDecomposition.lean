module
public import SerrePositivity.KST.LocalizingInvariants.SquareDiagonalHomotopy

public import SerrePositivity.InfinityCategories.Core.Quasicategory.SquareDiagonalEdgeRestriction
public import SerrePositivity.KST.LocalizingInvariants.FiberDiagramRightRestriction
public import SerrePositivity.KST.LocalizingInvariants.FiberDiagramRightPrism

/-!
概要：元の fiber 比較の右辺を、元の下側・上側三角形の全 h Fun 合成に分解する。
方針：右辺へ制限した同じホモトピーに、正方形の対角分解を適用する。
規約：二つの Sp 二単体を元の rightLower/rightUpper と同定する。
使われ方：native 三角形正規化と BF 差の三角形の貼合せ。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.LocalizingInvariants.FiberDiagram

variable {D E : FiberDiagram.{u}} (f : D ⟶ E)

def rightComparisonHomotopy := stableHomotopyPrecomp squareRightEdge (comparisonHomotopy f)

def rightAfterBottom := SquareDiagonal.afterBottom (rightComparisonHomotopy f)

def rightBeforeTop := SquareDiagonal.beforeTop (rightComparisonHomotopy f)

lemma rightRestriction_decomposition : rightRestriction.map f =
    Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy (rightAfterBottom f)) ≫
      Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy (rightBeforeTop f)) := by
  rw [rightRestriction_map_homotopy]
  exact SquareDiagonal.homMk_decomposition (rightComparisonHomotopy f)

lemma domainRight_edge : SSet.yonedaEquiv (squareRightEdge : (Δ[1] : SSet.{u + 1}) ⟶ _) =
    domainRight.{u}.edge := by
  have he := squareRightArrow_edge (𝟙 ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1]))
  rw [Category.comp_id] at he
  exact he.symm

lemma rightUpper_triangle : SSet.yonedaEquiv
    (squareTriangle 0 ≫ (rightComparisonHomotopy f).h) = rightUpper f := by
  exact (SquareDiagonal.upper_restriction squareRightEdge (comparisonHomotopy f).h).trans
    (congrArg (F2.homotopyEdgeTriangleUpper (comparisonHomotopy f).h) domainRight_edge)

lemma rightLower_triangle : SSet.yonedaEquiv
    (squareTriangle 1 ≫ (rightComparisonHomotopy f).h) = rightLower f := by
  exact (SquareDiagonal.lower_restriction squareRightEdge (comparisonHomotopy f).h).trans
    (congrArg (F2.homotopyEdgeTriangleLower (comparisonHomotopy f).h) domainRight_edge)

end SerrePositivity.KST.LocalizingInvariants.FiberDiagram
