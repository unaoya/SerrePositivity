module
public import SerrePositivity.KST.SConstruction.StableZeroSquareTriangleRecovery
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SpecifiedComparisonRestrictionComposition

/-!
概要：元零四角形全比較の包含・商・零左側面の制限を指定同型そのものへ回収する。
方針：元全二胞体比較の回収と元二短辺の厳密制限を接続する。
規約：同型の存在ではなく同じ全比較の値を保持。使われ方：実右面の指定三境界。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet InfinityCategories LocalizingInvariants
open scoped Simplicial
variable {f g : (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u}}
  (H : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.SquareFrameHomotopy (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.ofSquare f) (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.ofSquare g))
  (hz : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.IsZeroCategory (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableObject (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex f 0 1)))

private lemma shortFaceEq (j : Fin 2) (i : Fin 3)
    (a : (Δ[1] : SSet.{u + 1}) ⟶ Δ[1] ⊗ Δ[1]) (ha : stdSimplex.δ i ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle j = a)
    (p : (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u}) :
    stdSimplex.δ i ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle j ≫ p = a ≫ p :=
  (Category.assoc _ _ _).symm.trans (congrArg (fun q => q ≫ p) ha)

/-- 概要：元全零四角形比較の下辺は同じ元指定包含全比較。
方針：元下二胞体比較と元前短辺の全制限を使う。
規約：元指定同型の値を保持。使われ方：全右面の包含境界。 -/
lemma stableZeroSquareComparison_bottom (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ f) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ g))
    (he : e.hom = Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H.bottom)) :
    (stableZeroSquareComparison H hz).precomp _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge = e := by
  apply eq_of_heq
  exact _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.specifiedFunctorIsoRestrictionFromTriangle (stableZeroSquareComparison H hz)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 1) (stdSimplex.δ (2 : Fin 3)) _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.stableSquareTriangle_bottomEdge rfl rfl (squareFrameTriangleComparison H 1)
    (stableZeroSquareComparison_lower H hz)
    (shortFaceEq 1 2 _ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.stableSquareTriangle_bottomEdge f)
    (shortFaceEq 1 2 _ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.stableSquareTriangle_bottomEdge g) e
    (specifiedHomotopyRestrictionIso (squareFrameTriangleHomotopy H 1)
      (squareFrameTriangleComparison H 1) rfl _ _ _ H.bottom e he
      (squareFrameTriangleHomotopy_faces H 1).1)

/-- 概要：元全零四角形比較の右辺は同じ元指定商全比較。
方針：元下二胞体比較と元後短辺の全制限を使う。
規約：元指定同型の値を保持。使われ方：全右面の商境界。 -/
lemma stableZeroSquareComparison_right (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ f) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ g))
    (he : e.hom = Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H.right)) :
    (stableZeroSquareComparison H hz).precomp _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge = e := by
  apply eq_of_heq
  exact _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.specifiedFunctorIsoRestrictionFromTriangle (stableZeroSquareComparison H hz)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 1) (stdSimplex.δ (0 : Fin 3)) _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTriangle_rightEdge rfl rfl (squareFrameTriangleComparison H 1)
    (stableZeroSquareComparison_lower H hz)
    (shortFaceEq 1 0 _ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTriangle_rightEdge f)
    (shortFaceEq 1 0 _ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTriangle_rightEdge g) e
    (specifiedHomotopyRestrictionIso (squareFrameTriangleHomotopy H 1)
      (squareFrameTriangleComparison H 1) rfl _ _ _ H.right e he
      (squareFrameTriangleHomotopy_faces H 1).2)

/-- 概要：元全零四角形比較の左辺は同じ元指定零左側面全比較。
方針：元上二胞体比較と元前短辺の全制限を使う。
規約：元指定同型の値を保持。使われ方：全右面の零角境界。 -/
lemma stableZeroSquareComparison_left (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge ≫ f) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge ≫ g))
    (he : e.hom = Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H.left)) :
    (stableZeroSquareComparison H hz).precomp _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge = e := by
  apply eq_of_heq
  exact _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.specifiedFunctorIsoRestrictionFromTriangle (stableZeroSquareComparison H hz)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 0) (stdSimplex.δ (2 : Fin 3)) _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.stableSquareTriangle_leftEdge rfl rfl (squareFrameTriangleComparison H 0)
    (stableZeroSquareComparison_upper H hz)
    (shortFaceEq 0 2 _ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.stableSquareTriangle_leftEdge f)
    (shortFaceEq 0 2 _ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.stableSquareTriangle_leftEdge g) e
    (specifiedHomotopyRestrictionIso (squareFrameTriangleHomotopy H 0)
      (squareFrameTriangleComparison H 0) rfl _ _ _ H.left e he
      (squareFrameTriangleHomotopy_faces H 0).1)
end SerrePositivity.KST.SConstruction
