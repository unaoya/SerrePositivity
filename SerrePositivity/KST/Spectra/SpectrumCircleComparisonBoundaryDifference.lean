module

public import SerrePositivity.KST.Spectra.SpectrumCircleComparisonCorners
public import SerrePositivity.KST.Spectra.SpectrumCircleComparisonRightEdges
public import SerrePositivity.InfinityCategories.Project.PointedSpaces.FramedSquareDifference
public import SerrePositivity.KST.Spectra.FundamentalLoopHomotopyCategory

/-!
概要：元の比較 Hom 正方形の共通下辺を消去し、右辺の差を元の companion loop へ同定する。
方針：元の隅の等式を指定して二つの実際の正方形の境界の合成を比較する。
規約：元の比較三単体の全 Hom と基点を保持。使われ方：apex 射の成分の符号計算。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped _root_.Simplicial
namespace SerrePositivity.KST.Spectra.OmegaSpectrum
local instance circleComparisonDifferenceHomKan (z : Sp.{u} _⦋0⦌) :
    KanComplex (circleEvaluationPointedHom z).right := by
  change KanComplex (mappingSpace
    (cotensor PointedSimplicialSet.circle (nativeCotensorInput PointedSimplicialSet.circle z).val)
    (nativeCotensorInput PointedSimplicialSet.circle z).val)
  infer_instance
local instance circleComparisonDifferenceEdgeIso (z : Sp.{u} _⦋0⦌)
    {a b : (circleEvaluationPointedHom z).right _⦋0⦌}
    (e : (circleEvaluationPointedHom z).right.Edge a b) :
    IsIso (SSet.HomotopyCategory.homMk e) :=
  IsGroupoid.all_isIso (C := hoFunctor.obj (circleEvaluationPointedHom z).right) _

/-- 元の右辺を、共通の元の右下頂点から零頂点への辺として表示する。 -/
def circleCompanionComparisonRightEdge (z : Sp.{u} _⦋0⦌) (k : Limits.WalkingPair) :
    (circleEvaluationPointedHom z).right.Edge
      (circleCompanionComparisonMiddleVertex z) (circleEvaluationPointedHom z).basepoint :=
  _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.right (circleCompanionComparisonRawHomSquare z k)
    (circleEvaluationPointedHom z).basepoint (circleCompanionComparisonMiddleVertex z)
    (circleCompanionComparisonRawHomSquare_middle_corner z k)
    (circleCompanionComparisonRawHomSquare_top_corner z k 1)

/-- 元の比較正方形の左辺は、元の companion の境界定数一単体の辺そのもの。 -/
lemma circleCompanionComparisonLeftEdge (z : Sp.{u} _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.left (circleCompanionComparisonRawHomSquare z .left)
      (circleEvaluationPointedHom z).basepoint
      (circleCompanionComparisonRawHomSquare_left_corner z .left 0)
      (circleCompanionComparisonRawHomSquare_left_corner z .left 1) =
    FundamentalLoop.edge (circleEvaluationCompanionSimplex z) := by
  apply SSet.Edge.ext
  have h := congrArg SSet.yonedaEquiv
    (circleCompanionComparisonRawHomSquare_skipFirst_left z)
  rw [← _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SquareBoundaryComposition.left_yoneda, SSet.yonedaEquiv_comp, Equiv.apply_symm_apply] at h
  exact h

/-- 元の右辺の差は、同じ元の基点の companion loop の基本群の像。 -/
lemma circleCompanionComparisonBoundary_difference (z : Sp.{u} _⦋0⦌) :
    inv (SSet.HomotopyCategory.homMk (circleCompanionComparisonRightEdge z .right)) ≫
      SSet.HomotopyCategory.homMk (circleCompanionComparisonRightEdge z .left) =
    FundamentalLoop.toHom (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk (circleEvaluationCompanionSimplex z)) := by
  have h := _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.difference
    (circleCompanionComparisonRawHomSquare z .left)
    (circleCompanionComparisonRawHomSquare z .right)
    (circleEvaluationPointedHom z).basepoint (circleCompanionComparisonMiddleVertex z)
    (circleCompanionComparisonRawHomSquare_left_corner z .left 0)
    (circleCompanionComparisonRawHomSquare_middle_corner z .left)
    (circleCompanionComparisonRawHomSquare_left_corner z .left 1)
    (circleCompanionComparisonRawHomSquare_top_corner z .left 1)
    (circleCompanionComparisonRawHomSquare_left_corner z .right 0)
    (circleCompanionComparisonRawHomSquare_middle_corner z .right)
    (circleCompanionComparisonRawHomSquare_left_corner z .right 1)
    (circleCompanionComparisonRawHomSquare_top_corner z .right 1)
    (circleCompanionComparisonRawHomSquare_skipSecond_common z)
    (circleCompanionComparisonRawHomSquare_includeSecond z .left)
    (circleCompanionComparisonRawHomSquare_includeSecond z .right)
    (circleCompanionComparisonRawHomSquare_skipFirst_right z)
  rw [circleCompanionComparisonLeftEdge] at h
  exact h

end SerrePositivity.KST.Spectra.OmegaSpectrum
