module
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.BoundaryFaces
public import SerrePositivity.KST.SConstruction.MappingSquareCornerIdentities

/-! # 三つの元の辺を貼った全三角形境界
概要：端点が合う三辺を、全三角形境界からの実射へ貼る。
方針：境界の三面の余極限表示を使い、三つの共通頂点で互換性を照合する。
規約：三辺の全区間を変更せず、標的の充填性は仮定しない。
使われ方：全三辺を固定する指定三角形の相対延長。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open Spectra
open scoped Simplicial
variable {E : SSet.{u}} {a b c : E _⦋0⦌}
  (f : E.Edge a b) (g : E.Edge b c) (h : E.Edge a c)

/-- 三つの元の区間を、面番号の順に並べる。 -/
def triangleBoundaryFaces : Fin 3 → ((Δ[1] : SSet.{u}) ⟶ E) :=
  ![SSet.yonedaEquiv.symm g.edge, SSet.yonedaEquiv.symm h.edge,
    SSet.yonedaEquiv.symm f.edge]

/-- 三辺の共通端点が、全境界面族の互換性を与える。 -/
lemma triangleBoundaryFaces_compatible :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.IsCompatible (triangleBoundaryFaces f g h) := by
  intro j k hjk
  fin_cases j
  · fin_cases k
    · exact False.elim ((by decide : ¬ ((0 : Fin 3) < 0)) hjk)
    · change stdSimplex.δ 0 ≫ SSet.yonedaEquiv.symm g.edge =
        stdSimplex.δ 0 ≫ SSet.yonedaEquiv.symm h.edge
      rw [SSet.Edge.δ_zero_yonedaEquiv_symm,
        SSet.Edge.δ_zero_yonedaEquiv_symm]
    · change stdSimplex.δ 1 ≫ SSet.yonedaEquiv.symm g.edge =
        stdSimplex.δ 0 ≫ SSet.yonedaEquiv.symm f.edge
      rw [SSet.Edge.δ_one_yonedaEquiv_symm,
        SSet.Edge.δ_zero_yonedaEquiv_symm]
  · fin_cases k
    · exact False.elim ((by decide : ¬ ((1 : Fin 3) < 0)) hjk)
    · exact False.elim ((by decide : ¬ ((1 : Fin 3) < 1)) hjk)
    · change stdSimplex.δ 1 ≫ SSet.yonedaEquiv.symm h.edge =
        stdSimplex.δ 1 ≫ SSet.yonedaEquiv.symm f.edge
      rw [SSet.Edge.δ_one_yonedaEquiv_symm,
        SSet.Edge.δ_one_yonedaEquiv_symm]
  · fin_cases k
    · exact False.elim ((by decide : ¬ ((2 : Fin 3) < 0)) hjk)
    · exact False.elim ((by decide : ¬ ((2 : Fin 3) < 1)) hjk)
    · exact False.elim ((by decide : ¬ ((2 : Fin 3) < 2)) hjk)

/-- 三つの元の辺を全体として含む、全三角形境界からの実写像。 -/
def triangleBoundaryMap : (∂Δ[2] : SSet.{u}) ⟶ E :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.desc (triangleBoundaryFaces_compatible f g h)

/-- 全境界の各面は、元の同じ区間。 -/
lemma triangleBoundaryMap_face (i : Fin 3) :
    boundary.ι i ≫ triangleBoundaryMap f g h = triangleBoundaryFaces f g h i :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.ι_desc _ i

end SerrePositivity.KST.SConstruction
