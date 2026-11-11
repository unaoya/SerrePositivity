module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CoherentTetrahedronBoundary

/-!
概要：指定辺と読み戻した射の型を含む一致。
方針：端点と境界射の等式を消去して指定データを比較する。
規約：単に別の同型の存在を示すのでなく元の値を保持する。
使われ方：四面の合成則を任意に指定した境界関手へ移す。

対応節は Kerodon 5.5（Tag 01YV）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC

/-- 概要：指定射の coherent 辺と等しい辺の読み戻しは元の射と等しい。
方針：端点と読み戻しの等式を消去する。
規約：対象の等式による型の変化を許す。
使われ方：三角形・四面の同型を共通の境界へ揃える。 -/
lemma coherentEdgeHom_of_edge_eq {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {X Y : C} {s : (SimplicialNerve C) _⦋1⦌} {f : X ⟶ Y}
    (h : s = (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge f).edge) : HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentEdgeHom s) f :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentEdgeHom_heq h).trans (heq_of_eq (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentEdgeHom_edge f))

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
