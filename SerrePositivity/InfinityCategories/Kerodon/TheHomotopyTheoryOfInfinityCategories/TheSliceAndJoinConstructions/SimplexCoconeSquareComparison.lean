module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.SimplexCoconeSquareComparison

public import SerrePositivity.KST.LocalizingInvariants.SimplexCoconeComparison
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SuspensionSpanComparison

/-!
概要：元の実比較四角形の四辺を使い、指定前段経路を保つ全単体比較を貼る。
方針：四角形の実二単体から合成類の等式を証明し、既存の共有経路付き貼合せへ入力する。
規約：四辺の照合は端点の正規化を含む Arrow の等式。経路の選び直しを要求しない。
使われ方：分数評価四角形と回収 Hom 比較から、全パラメータの単体比較へ進む。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants

/-- 元の四角形から合成整合を放電し、指定前段経路を保つ全単体比較を貼る。 -/
lemma exists_simplexCoconeComparison_of_square {X : SSet.{u}} [Quasicategory X] {n : ℕ}
    {F G : (Δ[n] : SSet.{u}) ⟶ X} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone F) (d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone G)
    (a : SSet.Edge (X := (ihom (Δ[n] : SSet.{u})).obj X) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex G))
    (w : SSet.Edge c.vertex d.vertex)
    (ha : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge a.toTruncated) (hw : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge w.toTruncated)
    (S : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X)
    (hf : Arrow.mk (Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareBottomArrow S)) =
      Arrow.mk (Truncated.HomotopyCategory.homMk
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeVertexLeg c (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.simplexLastPoint n))).toTruncated))
    (hg : Arrow.mk (Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareTopArrow S)) =
      Arrow.mk (Truncated.HomotopyCategory.homMk
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeVertexLeg d (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.simplexLastPoint n))).toTruncated))
    (hs : Arrow.mk (Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareLeftArrow S)) =
      Arrow.mk (Truncated.HomotopyCategory.homMk
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.functorEdgeAt a (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.simplexLastPoint n))).toTruncated))
    (ht : Arrow.mk (Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareRightArrow S)) =
      Arrow.mk (Truncated.HomotopyCategory.homMk w.toTruncated)) :
    ∃ l : Truncated.Edge
        (X := (truncation 2).obj ((ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[n] : SSet.{u}) Δ[0])).obj X))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex c.val) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex d.val),
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (X := (ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[n] : SSet.{u}) Δ[0])).obj X) l ∧
      ((pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[n] : SSet.{u}) Δ[0])).app X).app
        (Opposite.op ⦋1⦌) l.edge = a.edge ∧
      SSet.yonedaEquiv.symm l.edge ≫ (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[n] : SSet.{u}) Δ[0])).app X =
        curry (CartesianMonoidalCategory.snd (Δ[0] : SSet.{u}) Δ[1] ≫
          SSet.yonedaEquiv.symm w.edge) := by
  apply exists_simplexCoconeComparison c d a w ha hw
  exact _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.spanSquare_homMk_comm_of_arrowMks S _ _ _ _ hf hg hs ht

end SerrePositivity.KST.LocalizingInvariants
