module
public import SerrePositivity.InfinityCategories.Stable.SquareHomotopyCategory

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
namespace SerrePositivity.InfinityCategories

def squareDiagonalArrow {X : SSet.{u}} (F : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X) :
    Truncated.Edge (X := (truncation 2).obj X)
      (squareVertex F 0 0) (squareVertex F 1 1) :=
  (homotopyIntervalEdge.tensor homotopyIntervalEdge).map ((truncation 2).map F)

lemma squareBottomRight_homMk_diagonal {X : SSet.{u}}
    (F : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X) :
    Truncated.HomotopyCategory.homMk (squareBottomArrow F) ≫
      Truncated.HomotopyCategory.homMk (squareRightArrow F) =
        Truncated.HomotopyCategory.homMk (squareDiagonalArrow F) := by
  exact Truncated.HomotopyCategory.homMk_comp_homMk
    (((Truncated.Edge.CompStruct.compId homotopyIntervalEdge).tensor
      (Truncated.Edge.CompStruct.idComp homotopyIntervalEdge)).map ((truncation 2).map F))

lemma squareLeftTop_homMk_diagonal {X : SSet.{u}}
    (F : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X) :
    Truncated.HomotopyCategory.homMk (squareLeftArrow F) ≫
      Truncated.HomotopyCategory.homMk (squareTopArrow F) =
        Truncated.HomotopyCategory.homMk (squareDiagonalArrow F) := by
  exact Truncated.HomotopyCategory.homMk_comp_homMk
    (((Truncated.Edge.CompStruct.idComp homotopyIntervalEdge).tensor
      (Truncated.Edge.CompStruct.compId homotopyIntervalEdge)).map ((truncation 2).map F))

end SerrePositivity.InfinityCategories
