module

public import SerrePositivity.InfinityCategories.F2.CatTriangleIso
public import SerrePositivity.InfinityCategories.F2.ConstantCoherentTriangle
public import SerrePositivity.InfinityCategories.F2.FunctorEqIso
public import SerrePositivity.InfinityCategories.F2.CatTriangleFacesEquality

/-!
概要：定値な coherent 三角形の指定同型の簡約。
方針：core の包含による定値辺の保存と恒等射を使う。
規約：指定された三角形と同型の値を保持する。
使われ方：引き戻し錐と指定 path の比較を簡約する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：定値な豊穣三角形の関手空間内の代表辺も定値。
方針：core の包含の定値辺に対する自然性を使う。
規約：指定された値を保持する。
使われ方：strict な比較三角形の同型の簡約。 -/
lemma catInfinityTriangleEdge_constant (s : CatInfinity.{u} _⦋2⦌)
    (hs : IsConstantCoherentTriangle s) :
    (catInfinityTriangleEdge s).edge = PinchedHom.constant
      (functorVertex (coherentEdgeHom (CatInfinity.δ 1 s))) 1 := by
  change (quasicategoryCore ((ihom (s.obj ⟨ULift.up 0⟩).obj).obj
    (s.obj ⟨ULift.up 2⟩).obj)).ι.app (Opposite.op ⦋1⦌) (coherentTriangleHomotopy s) = _
  rw [coherentTriangleHomotopy_constant_source s hs, pinchedConstant_map]
  exact congrArg (fun y ↦ PinchedHom.constant y 1) (qCatHom_vertex_ι _ _ _)
/-- 概要：定値な coherent 三角形の指定同型は等式から来る。
方針：指定代表辺の定値性を恒等射の判定に適用する。
規約：指定された値を保持する。
使われ方：strict な比較三角形の同型の簡約。 -/
lemma isFunctorEqIso_catInfinityTriangleIso (s : CatInfinity.{u} _⦋2⦌)
    (hs : IsConstantCoherentTriangle s) : IsFunctorEqIso (catInfinityTriangleIso s) :=
  isFunctorEqIso_of_constant_edge _ _ (catInfinityTriangleIso_hom s)
    (catInfinityTriangleEdge_constant s hs)

end SerrePositivity.InfinityCategories.F2
