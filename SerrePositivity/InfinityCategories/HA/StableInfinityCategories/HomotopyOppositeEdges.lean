module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.HomotopyOpposite
public import SerrePositivity.InfinityCategories.HA.Section6_1_1.SquareDuality
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.PastingSplitProjection

/-! # 反対ホモトピー圏の比較と辺

概要：反対圏との比較同値は辺を元へ戻す操作を保つ。
方針：辺の類への標準比較を展開し、双対四角形の辺を計算する。
規約：頂点の反転を含む厳密な式。使われ方：引き戻しから二項積を得る。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 概要：反対ホモトピー圏の比較同値は辺の類を元へ戻した辺の反対射に送る。
方針：道から辺の類への比較を辺の生成元上で計算する。
規約：元の X は quasicategory。使われ方：普遍二項余錐の双対化。 -/
lemma homotopyOppositeEquivalence_map_homMk {X : SSet.{u}} [Quasicategory X]
    {x y : X.op _⦋0⦌}
    (e : SSet.Truncated.Edge (X := (truncation 2).obj X.op) x y) :
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.homotopyOppositeEquivalence X).functor.map (SSet.Truncated.HomotopyCategory.homMk e) =
      (SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.edgeUnop (X := X) e)).op := by
  change ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.edgeToPathHomotopyCategory ((truncation 2).obj X)).map
    (((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.edgeHomotopyUnopFunctor X).map
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.pathToEdgeHomotopyCategory ((truncation 2).obj X.op)).map
        (SSet.Truncated.HomotopyCategory.homMk e))).unop)).op = _
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.pathToEdgeHomotopyCategory, SSet.Truncated.HomotopyCategory.lift_map_homMk,
    SSet.Truncated.HomotopyCategory₂.homMk]
  rfl

/-- 概要：双対四角形の右辺を元へ戻すと元の下辺になる。
方針：一次単体の反転と二座標の反転を計算する。
規約：端点も同時に一致する。使われ方：二項積の第一射影。 -/
lemma edgeUnop_dualSquare_right {X : SSet.{u}}
    (R : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.edgeUnop (X := X) (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareRightArrow (_root_.SerrePositivity.InfinityCategories.HA.Section6_1_1.dualSquare R)) = _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareBottomArrow R := by
  apply SSet.Truncated.Edge.ext
  change R.app _ (_, _) = R.app _ (_, _)
  congr 1
  apply Prod.ext <;> apply stdSimplex.ext <;> intro i <;> fin_cases i <;> rfl

/-- 概要：双対四角形の上辺を元へ戻すと元の左辺になる。
方針：一次単体の反転と二座標の反転を計算する。
規約：端点も同時に一致する。使われ方：二項積の第二射影。 -/
lemma edgeUnop_dualSquare_top {X : SSet.{u}}
    (R : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.edgeUnop (X := X) (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareTopArrow (_root_.SerrePositivity.InfinityCategories.HA.Section6_1_1.dualSquare R)) = _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareLeftArrow R := by
  apply SSet.Truncated.Edge.ext
  change R.app _ (_, _) = R.app _ (_, _)
  congr 1
  apply Prod.ext <;> apply stdSimplex.ext <;> intro i <;> fin_cases i <;> rfl

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
