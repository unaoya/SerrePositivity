module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.VertexIsoTerminalEquality
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.UnstraighteningConstantVertices
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.VertexIsoMappingLaws

/-!
概要：定値に一致する元の全族への指定同型の像は、同じ指定頂点の恒等同型となる。
方針：元の写像の等式と定値写像の同型の像を使い、頂点表示だけを揃える。
規約：指定同型の値を保持。使われ方：全初期値固定の辺比較の native 始点像。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 元の定値族に一致する全写像の像は、同じ元の指定頂点の恒等同型。 -/
lemma vertexIso_map_heq_refl_of_eq_const {X Y : SSet.{u}} [Quasicategory X]
    {x y : X _⦋0⦌} (e : VertexIso x y) {f : X ⟶ Y} (b : Y _⦋0⦌)
    (h : f = SSet.const b) : HEq (VertexIso.map e f) (Iso.refl (SSet.HomotopyCategory.mk b)) := by
  have hc := vertexIso_map_heq e h
  rw [VertexIso.map_const] at hc
  have hr {a b : hoFunctor.obj Y} (h : a = b) : HEq (Iso.refl a) (Iso.refl b) := by
    cases h
    rfl
  exact hc.trans (hr (congrArg SSet.HomotopyCategory.mk (constMap_vertex_value b x)))

end SerrePositivity.InfinityCategories.F2
