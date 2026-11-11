module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.SpaceTetrahedronWhiskerEdges
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.SpaceTriangleIso
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FunctorIsoTransport

/-!
概要：三単体の四面から共通の六関手の関手同型を読む。
方針：元の三角形の指定辺を両端だけ輸送して同型にする。
規約：別の辺の代表を選択しない。
使われ方：指定関手同型の前後合成の等式。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：面 013 の指定辺から共通の境界関手間の同型を作る。
方針：元の三角形の同型を境界関手の等式によって輸送する。
規約：順方向の射は指定された辺の類そのもの。
使われ方：四面の関手同型の合成則。 -/
def spaceInfinityTetrahedronIso013 (s : SpaceInfinity.{u} _⦋3⦌) :
    FunctorIso (spaceInfinityTetrahedron03 s)
      (spaceInfinityTetrahedron01 s ≫ spaceInfinityTetrahedron13 s) :=
  functorIsoOfEq (spaceInfinityTriangleIso (SpaceInfinity.δ 2 s)) rfl
    (congrArg (fun f ↦ spaceInfinityTetrahedron01 s ≫ f)
      (coherentTetrahedronBoundary13 s))
/-- 概要：面 023 の指定辺から共通の境界関手間の同型を作る。
方針：元の三角形の同型を境界関手の等式によって輸送する。
規約：順方向の射は指定された辺の類そのもの。
使われ方：四面の関手同型の合成則。 -/
def spaceInfinityTetrahedronIso023 (s : SpaceInfinity.{u} _⦋3⦌) :
    FunctorIso (spaceInfinityTetrahedron03 s)
      (spaceInfinityTetrahedron02 s ≫ spaceInfinityTetrahedron23 s) :=
  functorIsoOfEq (spaceInfinityTriangleIso (SpaceInfinity.δ 1 s)) (coherentTetrahedronBoundary03 s)
    (congrArg₂ (fun f g ↦ f ≫ g)
      (coherentTetrahedronBoundary02 s) (coherentTetrahedronBoundary23 s))
/-- 概要：面 012 の指定辺から共通の境界関手間の同型を作る。
方針：元の三角形の同型を境界関手の等式によって輸送する。
規約：順方向の射は指定された辺の類そのもの。
使われ方：四面の関手同型の合成則。 -/
def spaceInfinityTetrahedronIso012 (s : SpaceInfinity.{u} _⦋3⦌) :
    FunctorIso (spaceInfinityTetrahedron02 s)
      (spaceInfinityTetrahedron01 s ≫ spaceInfinityTetrahedron12 s) :=
  functorIsoOfEq (spaceInfinityTriangleIso (SpaceInfinity.δ 3 s)) rfl
    (congrArg₂ (fun f g ↦ f ≫ g)
      (coherentTetrahedronBoundary01 s) (coherentTetrahedronBoundary12 s))

end SerrePositivity.InfinityCategories.F2
