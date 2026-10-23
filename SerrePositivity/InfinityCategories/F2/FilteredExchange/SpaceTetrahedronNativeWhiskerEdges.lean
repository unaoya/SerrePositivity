module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.SpaceTetrahedronTriangles

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
def spaceInfinityTetrahedronPre123Native (s : SpaceInfinity.{u} _⦋3⦌) :
    ((ihom (s.obj ⟨ULift.up 0⟩).obj).obj (s.obj ⟨ULift.up 3⟩).obj).Edge
      (functorVertex (spaceInfinityTetrahedron01 s ≫ spaceInfinityTetrahedron13 s))
      (functorVertex ((spaceInfinityTetrahedron01 s ≫ spaceInfinityTetrahedron12 s) ≫
        spaceInfinityTetrahedron23 s)) :=
  ((spaceInfinityTriangleEdge (SpaceInfinity.δ 0 s)).map
    ((pre (show (s.obj ⟨ULift.up 0⟩).obj ⟶ (s.obj ⟨ULift.up 1⟩).obj from
      spaceInfinityTetrahedron01 s)).app (s.obj ⟨ULift.up 3⟩).obj)).ofEq rfl
      (by
        change functorVertex (spaceInfinityTetrahedron01 s ≫
          (spaceInfinityTetrahedron12 s ≫ spaceInfinityTetrahedron23 s)) = _
        rw [Category.assoc])
/-- 概要：面 012 の辺に元の関手 23 を後合成する。
方針：同じ境界射と前後合成の単体の式を使う。
規約：元の三角形の一単体を変更しない。
使われ方：四面の合成則を同じ四隅で比較する。 -/
def spaceInfinityTetrahedronPost012Native (s : SpaceInfinity.{u} _⦋3⦌) :
    ((ihom (s.obj ⟨ULift.up 0⟩).obj).obj (s.obj ⟨ULift.up 3⟩).obj).Edge
      (functorVertex (spaceInfinityTetrahedron02 s ≫ spaceInfinityTetrahedron23 s))
      (functorVertex ((spaceInfinityTetrahedron01 s ≫ spaceInfinityTetrahedron12 s) ≫
        spaceInfinityTetrahedron23 s)) :=
  ((spaceInfinityTetrahedronTriangle012 s).map
    ((ihom (s.obj ⟨ULift.up 0⟩).obj).map (spaceInfinityTetrahedron23 s))).ofEq rfl rfl
/-- 概要：精密化 013 から全 path への辺は指定された前合成の辺。
方針：同じ境界射と前後合成の単体の式を使う。
規約：元の三角形の一単体を変更しない。
使われ方：四面の合成則を同じ四隅で比較する。 -/
lemma spaceInfinityTetrahedronPre123Native_edge (s : SpaceInfinity.{u} _⦋3⦌) :
    (coherentTetrahedronHomEdge s coherentTetrahedronRefine013Full).edge =
      (spaceInfinityTetrahedronPre123Native s).edge :=
  spaceTetrahedron_face_zero s

/-- 概要：精密化 023 から全 path への辺は指定された後合成の辺。
方針：同じ境界射と前後合成の単体の式を使う。
規約：元の三角形の一単体を変更しない。
使われ方：四面の合成則を同じ四隅で比較する。 -/
lemma spaceInfinityTetrahedronPost012Native_edge (s : SpaceInfinity.{u} _⦋3⦌) :
    (coherentTetrahedronHomEdge s coherentTetrahedronRefine023Full).edge =
      (spaceInfinityTetrahedronPost012Native s).edge := by
  have h := spaceTetrahedron_face_three s
  change _ = ((ihom (s.obj ⟨ULift.up 0⟩).obj).map
    (coherentEdgeHom (SpaceInfinity.δ 0 (SpaceInfinity.δ 1 s)))).app (Opposite.op ⦋1⦌) _ at h
  have h23 : coherentEdgeHom (SpaceInfinity.δ 0 (SpaceInfinity.δ 1 s)) =
      spaceInfinityTetrahedron23 s := coherentTetrahedronBoundary23 s
  rw [h23] at h
  exact h

end SerrePositivity.InfinityCategories.F2
