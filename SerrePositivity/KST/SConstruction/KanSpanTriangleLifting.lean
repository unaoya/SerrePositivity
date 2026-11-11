module
public import SerrePositivity.KST.SConstruction.KanFibrationTriangleLifting
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanMappingSpanComposition

/-! # 境界で指定した逆・合成三角形を保つ span の相対充填
概要：span の第一辺の逆三角形と合成三角形を、指定した基底二単体のまま持ち上げる。
方針：逆は外側ホーン、合成は内側ホーンで逐次充填する。
規約：第一辺の一つの逆三角形と合成三角形を保存する。任意の二つの逆三角形の拡張は仮定しない。
使われ方：全パラメータ族を境界で既に指定した合成へ合わせる。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial

/-- span を一本の辺にする、一つの逆三角形と実合成三角形のデータ。 -/
structure KanSpanTriangleData {E : SSet.{u}} {z x y : E _⦋0⦌}
    (a : E.Edge z x) (b : E.Edge z y) where
  /-- 元の第一辺を逆向きにたどる辺。 -/
  inverse : E.Edge x z
  /-- 第一辺と逆辺の指定した実逆三角形。 -/
  inverseTriangle : SSet.Edge.CompStruct a inverse (SSet.Edge.id z)
  /-- span から得た実合成辺。 -/
  edge : E.Edge x y
  /-- 逆辺・元の第二辺・合成辺を保持する実三角形。 -/
  compositionTriangle : SSet.Edge.CompStruct inverse b edge

/-- 点ごとの両逆三角形付きのデータから、相対充填に必要な二つの三角形を保持する。 -/
def kanSpanTriangleDataOfComposition {E : SSet.{u}} {z x y : E _⦋0⦌}
    {a : E.Edge z x} {b : E.Edge z y} (t : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanMappingSpanComposition a b) :
    KanSpanTriangleData a b :=
  ⟨t.inverse, t.inverseLeft, t.edge, t.triangle⟩

/-- 基底の逆辺・合成辺と二つの二単体を全て厳密に回収する span の相対持ち上げ。 -/
lemma exists_kanSpanTriangleData_lift {E B : SSet.{u}} (q : E ⟶ B) [Fibration q]
    {z x y : E _⦋0⦌} (a : E.Edge z x) (b : E.Edge z y)
    (t : KanSpanTriangleData (a.map q) (b.map q)) :
    ∃ s : KanSpanTriangleData a b,
      q.app (Opposite.op ⦋1⦌) s.inverse.edge = t.inverse.edge ∧
      q.app (Opposite.op ⦋2⦌) s.inverseTriangle.simplex = t.inverseTriangle.simplex ∧
      q.app (Opposite.op ⦋1⦌) s.edge.edge = t.edge.edge ∧
      q.app (Opposite.op ⦋2⦌) s.compositionTriangle.simplex = t.compositionTriangle.simplex := by
  let tid : SSet.Edge.CompStruct (a.map q) t.inverse ((SSet.Edge.id z).map q) :=
    t.inverseTriangle.ofEq rfl rfl (congrArg SSet.Edge.edge (SSet.Edge.map_id z q)).symm
  obtain ⟨i, ti, hti, hi⟩ :=
    exists_kanFibration_liftOuterTriangle q a (SSet.Edge.id z) t.inverse tid
  let tc : SSet.Edge.CompStruct (i.map q) (b.map q) t.edge :=
    t.compositionTriangle.ofEq hi.symm rfl rfl
  obtain ⟨e, te, hte, he⟩ := exists_kanFibration_liftCompositionTriangle q i b t.edge tc
  exact ⟨⟨i, ti, e, te⟩, hi, hti, he, hte⟩

/-- 元の span のデータと、指定した基底の全辺・全三角形への厳密な射影。 -/
structure KanSpanTriangleDataOver {E B : SSet.{u}} (q : E ⟶ B)
    {z x y : E _⦋0⦌} (a : E.Edge z x) (b : E.Edge z y)
    (t : KanSpanTriangleData (a.map q) (b.map q)) where
  /-- 上の実際の逆・合成三角形。 -/
  data : KanSpanTriangleData a b
  /-- 元の指定逆辺の回収。 -/
  inverse_edge : q.app (Opposite.op ⦋1⦌) data.inverse.edge = t.inverse.edge
  /-- 元の指定逆三角形の回収。 -/
  inverse_triangle : q.app (Opposite.op ⦋2⦌) data.inverseTriangle.simplex =
    t.inverseTriangle.simplex
  /-- 元の指定合成辺の回収。 -/
  composite_edge : q.app (Opposite.op ⦋1⦌) data.edge.edge = t.edge.edge
  /-- 元の指定合成三角形の回収。 -/
  composition_triangle : q.app (Opposite.op ⦋2⦌) data.compositionTriangle.simplex =
    t.compositionTriangle.simplex

/-- 全ての指定辺と二単体を基底への厳密な射影として保持する持ち上げデータを選ぶ。 -/
def kanSpanTriangleDataLift {E B : SSet.{u}} (q : E ⟶ B) [Fibration q]
    {z x y : E _⦋0⦌} (a : E.Edge z x) (b : E.Edge z y)
    (t : KanSpanTriangleData (a.map q) (b.map q)) : KanSpanTriangleDataOver q a b t := by
  let hex := exists_kanSpanTriangleData_lift q a b t
  exact ⟨hex.choose, hex.choose_spec.1, hex.choose_spec.2.1,
    hex.choose_spec.2.2.1, hex.choose_spec.2.2.2⟩

end SerrePositivity.KST.SConstruction
