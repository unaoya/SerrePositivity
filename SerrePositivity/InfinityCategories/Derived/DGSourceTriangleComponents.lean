module
public import SerrePositivity.InfinityCategories.Derived.SourceTriangleComponents

/-! # 始点で前合成した三角形の対象と後辺

概要：前合成の対象族と後辺を元の三角形から回収する。
方針：任意の dg 圏に対して前合成データを一度評価する。
規約：具体的な dg 加群の巨大な成分を展開しない。使われ方：β3 の比較三単体。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D]

/-- 始点で前合成した対象族。 -/
lemma dgSourceTriangle_obj (s : Simplex A D 2) {X : D}
    (f : zeroCycles (homObject A D X (s.obj 0))) (i : Fin 3) :
    (SourcePrecomposition.simplex s f).obj i = Fin.cases X (fun j => s.obj j.succ) i := rfl

/-- 前合成は後の辺を保つ。 -/
lemma dgSourceTriangle_edge12 (s : Simplex A D 2) {X : D}
    (f : zeroCycles (homObject A D X (s.obj 0))) :
    (SourcePrecomposition.simplex s f).toSimplexData.edgeHom 1 2 (by decide) =
      s.toSimplexData.edgeHom 1 2 (by decide) := rfl

end SerrePositivity.InfinityCategories
