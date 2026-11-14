module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.SquareHomotopyCategory

/-!
概要：実比較正方形の対角辺を保ったまま、同じ cospan の普遍錐を構成する。
方針：端点で可逆なホモトピーによる矢印圏の同値と、厳密な錐の輸送を使う。
規約：一般安定性を仮定しない。使われ方：切除判定の第二条件と実 θ の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

def squareDiagonalArrow {X : SSet.{u}} (F : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X) :
    Truncated.Edge (X := (truncation 2).obj X)
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex F 0 0) (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex F 1 1) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.tensor _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge).map ((truncation 2).map F)

lemma squareBottomRight_homMk_diagonal {X : SSet.{u}}
    (F : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X) :
    Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareBottomArrow F) ≫
      Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareRightArrow F) =
        Truncated.HomotopyCategory.homMk (squareDiagonalArrow F) := by
  exact Truncated.HomotopyCategory.homMk_comp_homMk
    (((Truncated.Edge.CompStruct.compId _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge).tensor
      (Truncated.Edge.CompStruct.idComp _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge)).map ((truncation 2).map F))

lemma squareLeftTop_homMk_diagonal {X : SSet.{u}}
    (F : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X) :
    Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareLeftArrow F) ≫
      Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareTopArrow F) =
        Truncated.HomotopyCategory.homMk (squareDiagonalArrow F) := by
  exact Truncated.HomotopyCategory.homMk_comp_homMk
    (((Truncated.Edge.CompStruct.idComp _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge).tensor
      (Truncated.Edge.CompStruct.compId _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge)).map ((truncation 2).map F))

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
