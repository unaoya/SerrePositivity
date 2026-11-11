module
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.PushoutShape
public import Mathlib.AlgebraicTopology.SimplicialSet.Homotopy
public import Mathlib.CategoryTheory.Monoidal.Closed.Types
public import Mathlib.CategoryTheory.Monoidal.Limits.Preserves

/-! # 二つの三角柱から正方形のホモトピーを貼る

概要：対角で一致する上下三角形のホモトピーから正方形全体のホモトピーを作る。
方針：正方形の二セル表示の押し出しを Δ¹ との積で保存する。
規約：両端の正方形を厳密に保つ。使われ方：D7 の中間対象を零に送る比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories
open CategoryTheory MonoidalCategory
open scoped _root_.Simplicial

/-- 正方形の二三角形表示と区間の積も押し出し。 -/
lemma squarePrism_isPushout :
    IsPushout ((SSet.stdSimplex.δ (1 : Fin 3)) ▷ (Δ[1] : SSet.{u}))
      ((SSet.stdSimplex.δ (1 : Fin 3)) ▷ (Δ[1] : SSet.{u}))
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 0) ▷ (Δ[1] : SSet.{u})) ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 1) ▷ (Δ[1] : SSet.{u})) :=
  IsPushout.map (tensorRight (Δ[1] : SSet.{u})) _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.square_isPushout

variable {Y : SSet.{u}} {F G : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ Y}
variable (hU : SSet.Homotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 0 ≫ F) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 0 ≫ G))
variable (hL : SSet.Homotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 1 ≫ F) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 1 ≫ G))
variable (hdiag : ((SSet.stdSimplex.δ (1 : Fin 3)) ▷ (Δ[1] : SSet.{u})) ≫ hU.h =
  ((SSet.stdSimplex.δ (1 : Fin 3)) ▷ (Δ[1] : SSet.{u})) ≫ hL.h)

/-- 対角上で一致する二つの三角形ホモトピーを貼る。 -/
def squareHomotopyOfTriangleHomotopies : SSet.Homotopy F G where
  h := squarePrism_isPushout.desc hU.h hL.h hdiag
  h₀ := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.square_isPushout.hom_ext
    · rw [← Category.assoc, ← SSet.ι₀_comp, Category.assoc, squarePrism_isPushout.inl_desc]
      exact hU.h₀
    · rw [← Category.assoc, ← SSet.ι₀_comp, Category.assoc, squarePrism_isPushout.inr_desc]
      exact hL.h₀
  h₁ := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.square_isPushout.hom_ext
    · rw [← Category.assoc, ← SSet.ι₁_comp, Category.assoc, squarePrism_isPushout.inl_desc]
      exact hU.h₁
    · rw [← Category.assoc, ← SSet.ι₁_comp, Category.assoc, squarePrism_isPushout.inr_desc]
      exact hL.h₁
  rel := by
    ext n s
    exact False.elim s.1.2

/-- 貼った正方形ホモトピーは上側三角形のホモトピーを保つ。 -/
lemma squareHomotopyOfTriangleHomotopies_upper :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 0 ▷ (Δ[1] : SSet.{u})) ≫
      (squareHomotopyOfTriangleHomotopies hU hL hdiag).h = hU.h :=
  squarePrism_isPushout.inl_desc _ _ _

/-- 貼った正方形ホモトピーは下側三角形のホモトピーを保つ。 -/
lemma squareHomotopyOfTriangleHomotopies_lower :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 1 ▷ (Δ[1] : SSet.{u})) ≫
      (squareHomotopyOfTriangleHomotopies hU hL hdiag).h = hL.h :=
  squarePrism_isPushout.inr_desc _ _ _

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
