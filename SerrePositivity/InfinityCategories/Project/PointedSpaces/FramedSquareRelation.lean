module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Subdivision.SquareBoundaryComposition

/-!
概要：三つの隅を元の同一点に固定した正方形で、定値上辺を消去する。
方針：二つの元の三角形の合成構造を、指定された隅へ端点だけ移送する。
規約：元の辺の一単体を保持。使われ方：比較正方形の共通下辺の消去。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped _root_.Simplicial
namespace SerrePositivity.KST.Spectra.FramedSquare
end SerrePositivity.KST.Spectra.FramedSquare
namespace SerrePositivity.InfinityCategories.Project.PointedSpaces
open _root_.SerrePositivity.KST.Spectra
open _root_.SerrePositivity.KST.Spectra.FramedSquare
variable {X : SSet.{u}} (q : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X) (x y : X _⦋0⦌)
    (h00 : q.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SquareBoundaryComposition.corner 0 0) = x)
    (h10 : q.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SquareBoundaryComposition.corner 1 0) = y)
    (h01 : q.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SquareBoundaryComposition.corner 0 1) = x)
    (h11 : q.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SquareBoundaryComposition.corner 1 1) = x)

/-- 元の下辺を、指定された二つの隅に表示する。 -/
def bottom : X.Edge x y := (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SquareBoundaryComposition.bottom.map q).ofEq h00 h10

/-- 元の右辺を、指定された二つの隅に表示する。 -/
def right : X.Edge y x := (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SquareBoundaryComposition.right.map q).ofEq h10 h11

/-- 元の左辺を、元の基点の loop として表示する。 -/
def left : X.Edge x x := (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SquareBoundaryComposition.left.map q).ofEq h00 h01

/-- 元の上辺が定値なら、下辺と右辺の合成は元の左辺。 -/
lemma bottom_comp_right
    (ht : (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SquareBoundaryComposition.top.map q).edge = (X.σ 0) x) :
    SSet.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.bottom q x y h00 h10) ≫
      SSet.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.right q x y h10 h11) =
    SSet.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.left q x h00 h01) := by
  let d : X.Edge x x :=
    ((((_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.edge (0 : Fin 3) 2 (by decide)).map _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.upper).map q).ofEq
      h00 h11)
  have hu : SSet.Edge.CompStruct (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.left q x h00 h01) (SSet.Edge.id x) d :=
    (((_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.compStruct (0 : Fin 3) 1 2 (by decide) (by decide)).map
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.upper).map q).ofEq rfl ht rfl
  have hl : SSet.Edge.CompStruct (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.bottom q x y h00 h10) (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.right q x y h10 h11) d :=
    (((_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.compStruct (0 : Fin 3) 1 2 (by decide) (by decide)).map
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.lower).map q).ofEq rfl rfl
        (congrArg (fun e ↦ q.app (Opposite.op ⦋1⦌) e.edge) _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SquareBoundaryComposition.diagonal_edge.symm)
  have h := SSet.HomotopyCategory.homMk_comp_homMk hu
  erw [SSet.HomotopyCategory.homMk_id, Category.comp_id] at h
  exact (SSet.HomotopyCategory.homMk_comp_homMk hl).trans h.symm

/-- 上辺の定値写像の厳密式は、元の上辺の退化一単体の式を与える。 -/
lemma top_constant_edge
    (ht : lift (𝟙 (Δ[1] : SSet.{u}))
      (SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) ≫ q = SSet.const x) :
    (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SquareBoundaryComposition.top.map q).edge = (X.σ 0) x := by
  have h := congrArg SSet.yonedaEquiv ht
  rw [← _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SquareBoundaryComposition.top_yoneda, SSet.yonedaEquiv_comp, Equiv.apply_symm_apply] at h
  have hc := stdSimplex.yonedaEquiv_σ_comp
    (SSet.const x : (Δ[0] : SSet.{u}) ⟶ X) (0 : Fin 1)
  rw [SSet.comp_const, SSet.yonedaEquiv_const] at hc
  exact h.trans hc

end SerrePositivity.InfinityCategories.Project.PointedSpaces

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.bottom (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.FramedSquare.bottom := _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.bottom

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.FramedSquare.bottom_comp_right := _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.bottom_comp_right

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.left (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.FramedSquare.left := _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.left

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.right (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.FramedSquare.right := _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.right

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.FramedSquare.top_constant_edge := _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.top_constant_edge

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.FramedSquare.bottom._proof_1 := _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.bottom._proof_1
