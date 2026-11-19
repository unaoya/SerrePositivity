module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Subdivision.CompositionTripleTetrahedron

/-! # 元の合成三角形と指定比較面を保つ合成辺の置換
概要：元の合成面と、長辺を指定射へ比較する実三角形を同じ四面体の面に保持する。
方針：共有する恒等辺を含む内ホーンを貼り、残る実合成面を取り出す。
規約：元の指定比較面を類の等式に置換せず、全二単体を厳密に保持する。
使われ方：元の BF 境界比較を coherent nerve の実合成三角形へ渡す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
end SerrePositivity.KST.SConstruction
namespace SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries
open _root_.SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open scoped _root_.Simplicial

/-- 元の合成面と指定比較面を同時に保持する実四面体と新しい合成面。 -/
structure CompositionReplacementTetrahedron {E : SSet.{u}} {x y z : E _⦋0⦌}
    {a : E.Edge x y} {b : E.Edge y z} {c h : E.Edge x z}
    (original : SSet.Edge.CompStruct a b c)
    (replacement : SSet.Edge.CompStruct (SSet.Edge.id x) c h) where
  /-- 元の全三面を保持する実三単体。 -/
  simplex : E _⦋3⦌
  /-- 元の二射の合成三角形。 -/
  original_face : E.δ 0 simplex = original.simplex
  /-- 元の指定比較三角形。 -/
  replacement_face : E.δ 2 simplex = replacement.simplex
  /-- 共通の恒等辺を持つ同じ退化三角形。 -/
  unit_face : E.δ 3 simplex = (SSet.Edge.CompStruct.idComp a).simplex
  /-- 元の二辺と指定された長辺を持つ実合成面。 -/
  triangle : SSet.Edge.CompStruct a b h
  /-- 新しい面も同じ実四面体の面そのもの。 -/
  triangle_face : triangle.simplex = E.δ 1 simplex

/-- 元の全合成面・全指定比較面を保持して、同じ四面体の実合成面を構成する。 -/
def compositionReplacementTetrahedron {E : SSet.{u}} [Quasicategory E]
    {x y z : E _⦋0⦌} {a : E.Edge x y} {b : E.Edge y z} {c h : E.Edge x z}
    (original : SSet.Edge.CompStruct a b c)
    (replacement : SSet.Edge.CompStruct (SSet.Edge.id x) c h) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CompositionReplacementTetrahedron original replacement := by
  let T := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.compositionTripleTetrahedron (SSet.Edge.CompStruct.idComp a) original replacement
  exact ⟨T.simplex, T.second_face, T.right_face, T.first_face, T.left, T.left_face⟩

end SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
