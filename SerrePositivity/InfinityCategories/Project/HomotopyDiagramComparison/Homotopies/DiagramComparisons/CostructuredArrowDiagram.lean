module

public import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic
public import Mathlib.CategoryTheory.Category.Cat

/-!
# 元の中間射の comma 圏を終域に関する Cat 値図式へ束ねる

概要：Low 命題 3.7 の三本矢の右脚を動かす全図式を構成する。
方針：固定した左の関手に対する costructured arrow を元の後合成で送る。
規約：対象ごとの同値の選択を使わず、恒等と合成を厳密に保つ。
使われ方：三本矢の全図式の Grothendieck 表示。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v u' v'

namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison

open CategoryTheory

variable {K : Type u} [Category.{v} K] {C : Type u'} [Category.{v'} C]

/-- 概要：元の costructured arrow の圏は終域に関して関手的（Low 命題 3.7）。
方針：元の構造射への後合成と全可換三角形への恒等の左成分を使う。
規約：元の中間射・全射・厳密な恒等合成則を保持する。
使われ方：両脚の slice による三本矢の全図式。 -/
def costructuredArrowDiagram (Q : K ⥤ C) : C ⥤ Cat.{v, max u v'} where
  obj V := Cat.of (CostructuredArrow Q V)
  map r := (CostructuredArrow.map (S := Q) r).toCatHom
  map_id V := by
    apply Cat.Hom.ext
    exact CategoryTheory.Functor.ext (fun s => CostructuredArrow.map_id)
  map_comp r s := by
    apply Cat.Hom.ext
    exact CategoryTheory.Functor.ext (fun t => CostructuredArrow.map_comp)

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
