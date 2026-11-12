module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.IntervalFatDiagram

/-!
概要：端点を持つ実際の辺を、両端固定の区間写像空間の頂点として表示する。
方針：辺の Yoneda 射の境界を計算し、その関手頂点を制限の fiber へ入れる。
規約：単体集合の充填性は不要。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、写像空間の unstraightening 比較と一本の変換の作用の接続。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 概要：指定端点を持つ辺の Yoneda 射の境界は、その二端点を指定する区間境界図式。
方針：区間の境界の二つの面で確認する。
規約：時刻零が x、時刻一が y。
使われ方：Kerodon §4.6.6（Tag 04HY）、実際の辺を区間模型の頂点へ入れる条件。 -/
lemma intervalMappingBoundary_of_edge {X : SSet.{u}} {x y : X _⦋0⦌} (e : SSet.Edge x y) :
    (boundary 1).ι ≫ SSet.yonedaEquiv.symm e.edge = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingBoundary x y := by
  apply boundary.hom_ext
  intro i
  rw [← Category.assoc, boundary.ι_ι]
  apply SSet.yonedaEquiv.injective
  fin_cases i
  · rw [stdSimplex.yonedaEquiv_δ_comp, Equiv.apply_symm_apply, SSet.yonedaEquiv_comp]
    change X.δ 0 e.edge = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant y 0
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero]
    exact e.tgt_eq
  · rw [stdSimplex.yonedaEquiv_δ_comp, Equiv.apply_symm_apply, SSet.yonedaEquiv_comp]
    change X.δ 1 e.edge = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant x 0
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero]
    exact e.src_eq

/-- 概要：端点を持つ辺を区間写像空間の頂点にする。
方針：Yoneda 射の関手頂点に境界の固定条件を添える。
規約：辺の一単体そのものを保存する表示。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、個別の変換を写像空間の比較射へ入力する。 -/
def intervalMappingVertexOfEdge {X : SSet.{u}} {x y : X _⦋0⦌} (e : SSet.Edge x y) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace x y) _⦋0⦌ :=
  ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.yonedaEquiv.symm e.edge), by
    change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex ((boundary 1).ι ≫ SSet.yonedaEquiv.symm e.edge) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingBoundary x y)) 0
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero, intervalMappingBoundary_of_edge]⟩

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
