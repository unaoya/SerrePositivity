module

public import SerrePositivity.InfinityCategories.F2.SpaceTetrahedronNativeWhiskerEdges

/-!
概要：元の精密化の一次単体を保持した四面の前後合成の辺。
方針：前後合成した辺と同じ指定一次単体を明示して端点を保つ。
規約：一次単体の一致が定義上の等式となる表示を使う。
使われ方：四面の正方形の端点を同時に輸送する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：面 123 の前合成を元の精密化の一次単体で表す。
方針：対応する可逆な辺の両端と元の一次単体を使う。
規約：指定された一単体の代表を保つ。
使われ方：四面の合成関係の同時輸送。 -/
def spaceInfinityTetrahedronPre123 (s : SpaceInfinity.{u} _⦋3⦌) :
    ((ihom (s.obj ⟨ULift.up 0⟩).obj).obj (s.obj ⟨ULift.up 3⟩).obj).Edge
      (functorVertex (spaceInfinityTetrahedron01 s ≫ spaceInfinityTetrahedron13 s))
      (functorVertex ((spaceInfinityTetrahedron01 s ≫ spaceInfinityTetrahedron12 s) ≫
        spaceInfinityTetrahedron23 s)) :=
  edgeOfSimplexWithEndpoints (spaceInfinityTetrahedronPre123Native s)
    (coherentTetrahedronHomEdge s coherentTetrahedronRefine013Full).edge
    (spaceInfinityTetrahedronPre123Native_edge s) rfl rfl

/-- 概要：精密化の像の一次単体を定義上保持する。
方針：指定一次単体による辺の定義を読む。
規約：両端の正規化とは独立の厳密な等式。
使われ方：四面の正方形を同時に輸送する。 -/
lemma spaceInfinityTetrahedronPre123_edge (s : SpaceInfinity.{u} _⦋3⦌) :
    (coherentTetrahedronHomEdge s coherentTetrahedronRefine013Full).edge =
      (spaceInfinityTetrahedronPre123 s).edge := rfl
/-- 概要：面 012 の後合成を元の精密化の一次単体で表す。
方針：対応する可逆な辺の両端と元の一次単体を使う。
規約：指定された一単体の代表を保つ。
使われ方：四面の合成関係の同時輸送。 -/
def spaceInfinityTetrahedronPost012 (s : SpaceInfinity.{u} _⦋3⦌) :
    ((ihom (s.obj ⟨ULift.up 0⟩).obj).obj (s.obj ⟨ULift.up 3⟩).obj).Edge
      (functorVertex (spaceInfinityTetrahedron02 s ≫ spaceInfinityTetrahedron23 s))
      (functorVertex ((spaceInfinityTetrahedron01 s ≫ spaceInfinityTetrahedron12 s) ≫
        spaceInfinityTetrahedron23 s)) :=
  edgeOfSimplexWithEndpoints (spaceInfinityTetrahedronPost012Native s)
    (coherentTetrahedronHomEdge s coherentTetrahedronRefine023Full).edge
    (spaceInfinityTetrahedronPost012Native_edge s) rfl rfl

/-- 概要：精密化の像の一次単体を定義上保持する。
方針：指定一次単体による辺の定義を読む。
規約：両端の正規化とは独立の厳密な等式。
使われ方：四面の正方形を同時に輸送する。 -/
lemma spaceInfinityTetrahedronPost012_edge (s : SpaceInfinity.{u} _⦋3⦌) :
    (coherentTetrahedronHomEdge s coherentTetrahedronRefine023Full).edge =
      (spaceInfinityTetrahedronPost012 s).edge := rfl

end SerrePositivity.InfinityCategories.F2
