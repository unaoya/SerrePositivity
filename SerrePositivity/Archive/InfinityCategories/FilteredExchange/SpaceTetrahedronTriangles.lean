module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.SpaceTetrahedronArrows
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.SpecifiedSimplexEdge

/-!
概要：四面の三角形の端点を六関手で同時に記述する。
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

/-- 概要：面 013 を共通の辺 03 と合成 01・13 の辺として読む。
方針：同じ境界射と前後合成の単体の式を使う。
規約：元の三角形の一単体を変更しない。
使われ方：四面の合成則を同じ四隅で比較する。 -/
def spaceInfinityTetrahedronTriangle013 (s : SpaceInfinity.{u} _⦋3⦌) :
    ((ihom (s.obj ⟨ULift.up 0⟩).obj).obj (s.obj ⟨ULift.up 3⟩).obj).Edge
      (functorVertex (spaceInfinityTetrahedron03 s))
      (functorVertex (spaceInfinityTetrahedron01 s ≫ spaceInfinityTetrahedron13 s)) :=
  edgeOfSimplexWithEndpoints (spaceInfinityTriangleEdge (SpaceInfinity.δ 2 s))
    (coherentTetrahedronHomEdge s coherentTetrahedronRefine013).edge
    (spaceTetrahedron_face_two s) rfl
    (congrArg (fun f ↦ functorVertex (spaceInfinityTetrahedron01 s ≫ f))
      (coherentTetrahedronBoundary13 s))
/-- 概要：面 023 を共通の辺 03 と合成 02・23 の辺として読む。
方針：同じ境界射と前後合成の単体の式を使う。
規約：元の三角形の一単体を変更しない。
使われ方：四面の合成則を同じ四隅で比較する。 -/
def spaceInfinityTetrahedronTriangle023 (s : SpaceInfinity.{u} _⦋3⦌) :
    ((ihom (s.obj ⟨ULift.up 0⟩).obj).obj (s.obj ⟨ULift.up 3⟩).obj).Edge
      (functorVertex (spaceInfinityTetrahedron03 s))
      (functorVertex (spaceInfinityTetrahedron02 s ≫ spaceInfinityTetrahedron23 s)) :=
  edgeOfSimplexWithEndpoints (spaceInfinityTriangleEdge (SpaceInfinity.δ 1 s))
    (coherentTetrahedronHomEdge s coherentTetrahedronRefine023).edge
    (spaceTetrahedron_face_one s)
    (congrArg functorVertex (coherentTetrahedronBoundary03 s))
    (congrArg₂ (fun f g ↦ functorVertex (f ≫ g))
      (coherentTetrahedronBoundary02 s) (coherentTetrahedronBoundary23 s))
/-- 概要：面 012 を共通の辺 02 と合成 01・12 の辺として読む。
方針：同じ境界射と前後合成の単体の式を使う。
規約：元の三角形の一単体を変更しない。
使われ方：四面の合成則を同じ四隅で比較する。 -/
def spaceInfinityTetrahedronTriangle012 (s : SpaceInfinity.{u} _⦋3⦌) :
    ((ihom (s.obj ⟨ULift.up 0⟩).obj).obj (s.obj ⟨ULift.up 2⟩).obj).Edge
      (functorVertex (spaceInfinityTetrahedron02 s))
      (functorVertex (spaceInfinityTetrahedron01 s ≫ spaceInfinityTetrahedron12 s)) :=
  (spaceInfinityTriangleEdge (SpaceInfinity.δ 3 s)).ofEq rfl
    (congrArg₂ (fun f g ↦ functorVertex (f ≫ g))
      (coherentTetrahedronBoundary01 s) (coherentTetrahedronBoundary12 s))

end SerrePositivity.InfinityCategories.F2
