module

public import SerrePositivity.InfinityCategories.F2.CatInfinity.CatTetrahedronTriangles

/-!
概要：四面の指定辺の前後合成を共通の両端で表示する。
方針：境界の等式によって各面の指定辺の端点を揃える。
規約：頂点と一単体の代表を保つ。
使われ方：四面の指定関手同型の可換正方形。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：面 123 の辺に元の関手 01 を前合成する。
方針：同じ境界射と前後合成の単体の式を使う。
規約：元の三角形の一単体を変更しない。
使われ方：四面の合成則を同じ四隅で比較する。 -/
def catInfinityTetrahedronPre123Native (s : CatInfinity.{u} _⦋3⦌) :
    ((ihom (s.obj ⟨ULift.up 0⟩).obj).obj (s.obj ⟨ULift.up 3⟩).obj).Edge
      (functorVertex (catInfinityTetrahedron01 s ≫ catInfinityTetrahedron13 s))
      (functorVertex ((catInfinityTetrahedron01 s ≫ catInfinityTetrahedron12 s) ≫
        catInfinityTetrahedron23 s)) :=
  ((catInfinityTriangleEdge (CatInfinity.δ 0 s)).map
    ((pre (show (s.obj ⟨ULift.up 0⟩).obj ⟶ (s.obj ⟨ULift.up 1⟩).obj from
      catInfinityTetrahedron01 s)).app (s.obj ⟨ULift.up 3⟩).obj)).ofEq rfl
      (by
        change functorVertex (catInfinityTetrahedron01 s ≫
          (catInfinityTetrahedron12 s ≫ catInfinityTetrahedron23 s)) = _
        rw [Category.assoc])
/-- 概要：面 012 の辺に元の関手 23 を後合成する。
方針：同じ境界射と前後合成の単体の式を使う。
規約：元の三角形の一単体を変更しない。
使われ方：四面の合成則を同じ四隅で比較する。 -/
def catInfinityTetrahedronPost012Native (s : CatInfinity.{u} _⦋3⦌) :
    ((ihom (s.obj ⟨ULift.up 0⟩).obj).obj (s.obj ⟨ULift.up 3⟩).obj).Edge
      (functorVertex (catInfinityTetrahedron02 s ≫ catInfinityTetrahedron23 s))
      (functorVertex ((catInfinityTetrahedron01 s ≫ catInfinityTetrahedron12 s) ≫
        catInfinityTetrahedron23 s)) :=
  ((catInfinityTetrahedronTriangle012 s).map
    ((ihom (s.obj ⟨ULift.up 0⟩).obj).map (catInfinityTetrahedron23 s))).ofEq rfl rfl
/-- 概要：精密化 013 から全 path への辺は指定された前合成の辺。
方針：同じ境界射と前後合成の単体の式を使う。
規約：元の三角形の一単体を変更しない。
使われ方：四面の合成則を同じ四隅で比較する。 -/
lemma catInfinityTetrahedronPre123Native_edge (s : CatInfinity.{u} _⦋3⦌) :
    (catInfinityTetrahedronEdge s coherentTetrahedronRefine013Full).edge =
      (catInfinityTetrahedronPre123Native s).edge :=
  (catInfinityTetrahedron_face_zero s).trans (functorPrecomposition_simplex _ 1 _)
/-- 概要：精密化 023 から全 path への辺は指定された後合成の辺。
方針：同じ境界射と前後合成の単体の式を使う。
規約：元の三角形の一単体を変更しない。
使われ方：四面の合成則を同じ四隅で比較する。 -/
lemma catInfinityTetrahedronPost012Native_edge (s : CatInfinity.{u} _⦋3⦌) :
    (catInfinityTetrahedronEdge s coherentTetrahedronRefine023Full).edge =
      (catInfinityTetrahedronPost012Native s).edge := by
  have h := (catInfinityTetrahedron_face_three s).trans
    (functorPostcomposition_simplex _ 1 _)
  change _ = ((ihom (s.obj ⟨ULift.up 0⟩).obj).map
    (coherentEdgeHom (CatInfinity.δ 0 (CatInfinity.δ 1 s)))).app (Opposite.op ⦋1⦌) _ at h
  have h23 : coherentEdgeHom (CatInfinity.δ 0 (CatInfinity.δ 1 s)) =
      catInfinityTetrahedron23 s := coherentTetrahedronBoundary23 s
  rw [h23] at h
  exact h

end SerrePositivity.InfinityCategories.F2
