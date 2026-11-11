module
public import SerrePositivity.KST.SConstruction.SquareBoundaryEdgeCalculus
public import SerrePositivity.KST.SConstruction.ThreeSquarePasting

/-! # 全四辺を指定した写像空間の実正方形
概要：四つの元の辺を保持する正方形を、その二三角形の合成関係に渡す。
方針：境界射の Yoneda 表示を、標準三角形の raw な辺へ直接照合する。
規約：quasicategory 性を仮定せず、正方形全体をデータに残す。
使われ方：元の三正方形の境界から端点固定の合成比較を得る。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 指定した四辺を厳密に保つ、元の実正方形。 -/
structure MappingSquareBoundaryData {E : SSet.{u}} {a b c d : E _⦋0⦌}
    (bottom : E.Edge a b) (top : E.Edge c d) (left : E.Edge a c) (right : E.Edge b d) where
  /-- 元の正方形全体。 -/
  square : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ E
  /-- 下辺の厳密な回収。 -/
  bottom_eq : pastingSquareHorizontal 0 ≫ square = SSet.yonedaEquiv.symm bottom.edge
  /-- 上辺の厳密な回収。 -/
  top_eq : pastingSquareHorizontal 1 ≫ square = SSet.yonedaEquiv.symm top.edge
  /-- 左辺の厳密な回収。 -/
  left_eq : pastingSquareVertical 0 ≫ square = SSet.yonedaEquiv.symm left.edge
  /-- 右辺の厳密な回収。 -/
  right_eq : pastingSquareVertical 1 ≫ square = SSet.yonedaEquiv.symm right.edge

/-- 全四辺を指定した同じ正方形の、二三角形による合成の等号。 -/
lemma MappingSquareBoundaryData.homMk_comp {E : SSet.{u}} {a b c d : E _⦋0⦌}
    {bottom : E.Edge a b} {top : E.Edge c d} {left : E.Edge a c} {right : E.Edge b d}
    (Q : MappingSquareBoundaryData bottom top left right) :
    SSet.HomotopyCategory.homMk bottom ≫ SSet.HomotopyCategory.homMk right =
      SSet.HomotopyCategory.homMk left ≫ SSet.HomotopyCategory.homMk top := by
  apply _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.homMk_comp_eq_of_square bottom.toTruncated top.toTruncated
    left.toTruncated right.toTruncated Q.square
  · rw [squareHorizontalEdge_yoneda]
    change SSet.yonedaEquiv (pastingSquareHorizontal 0 ≫ Q.square) = bottom.edge
    rw [Q.bottom_eq, Equiv.apply_symm_apply]
  · rw [squareHorizontalEdge_yoneda]
    change SSet.yonedaEquiv (pastingSquareHorizontal 1 ≫ Q.square) = top.edge
    rw [Q.top_eq, Equiv.apply_symm_apply]
  · rw [squareVerticalEdge_yoneda]
    change SSet.yonedaEquiv (pastingSquareVertical 0 ≫ Q.square) = left.edge
    rw [Q.left_eq, Equiv.apply_symm_apply]
  · rw [squareVerticalEdge_yoneda]
    change SSet.yonedaEquiv (pastingSquareVertical 1 ≫ Q.square) = right.edge
    rw [Q.right_eq, Equiv.apply_symm_apply]

end SerrePositivity.KST.SConstruction
