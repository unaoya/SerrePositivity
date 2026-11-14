module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Triangles.SourceTriangleComponents

/-! # 始点で前合成した三角形の対象と後辺

概要：前合成の対象族と後辺を元の三角形から回収する。
方針：任意の dg 圏に対して前合成データを一度評価する。
規約：具体的な dg 加群の巨大な成分を展開しない。使われ方：β3 の比較三単体。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable {A : Type u} [CommRing A] {D : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory A D]

/-- 始点で前合成した対象族。 -/
lemma dgSourceTriangle_obj (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D 2) {X : D}
    (f : _root_.SerrePositivity.DifferentialGraded.zeroCycles (homObject A D X (s.obj 0))) (i : Fin 3) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SourcePrecomposition.simplex s f).obj i = Fin.cases X (fun j => s.obj j.succ) i := rfl

/-- 前合成は後の辺を保つ。 -/
lemma dgSourceTriangle_edge12 (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D 2) {X : D}
    (f : _root_.SerrePositivity.DifferentialGraded.zeroCycles (homObject A D X (s.obj 0))) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SourcePrecomposition.simplex s f).toSimplexData.edgeHom 1 2 (by decide) =
      s.toSimplexData.edgeHom 1 2 (by decide) := rfl

end SerrePositivity.InfinityCategories.Project.DerivedCategories
