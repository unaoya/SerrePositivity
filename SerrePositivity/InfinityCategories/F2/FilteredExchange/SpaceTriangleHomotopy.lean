module

public import SerrePositivity.InfinityCategories.F2.CatInfinity.CoherentTriangleEdge
public import SerrePositivity.InfinityCategories.Core.FunctorHomotopy
public import SerrePositivity.InfinityCategories.F1.Categories.CatInfinity

/-!
概要：𝒮 の二単体から元の Kan 射間の指定ホモトピーを読み戻す。
方針：coherent 精密化の辺を内部 Hom の辺として uncurry する。
規約：存在命題から代表を選び直さない。使われ方：native 錐の二次の可換性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：Kan 豊穣頂点は元の射の関手頂点。
方針：内部 Hom の単位の定義。規約：厳密な式。使われ方：両端の同定。 -/
lemma kanHom_vertex (X Y : KanObject.{u}) (f : X ⟶ Y) :
    SimplicialCategory.homEquiv' X Y f = functorVertex (show X.obj ⟶ Y.obj from f) := rfl

/-- 概要：𝒮 の二単体の元の精密化を関手空間の指定辺にする。
方針：両端だけを同定。規約：全一単体を保持。使われ方：三単体の合成則との比較。 -/
def spaceInfinityTriangleEdge (s : SpaceInfinity.{u} _⦋2⦌) :
    ((ihom (s.obj ⟨ULift.up 0⟩).obj).obj (s.obj ⟨ULift.up 2⟩).obj).Edge
      (functorVertex (coherentEdgeHom (SpaceInfinity.δ 1 s)))
      (functorVertex (coherentEdgeHom (SpaceInfinity.δ 2 s) ≫
        coherentEdgeHom (SpaceInfinity.δ 0 s))) :=
  (coherentTriangleEdge s).ofEq (kanHom_vertex _ _ _) (kanHom_vertex _ _ _)

/-- 概要：𝒮 の二単体を元の長辺と二辺の合成のホモトピーへ送る。
方針：指定精密化の辺をそのまま uncurry。規約：元の円柱。使われ方：錐の可換性。 -/
def spaceInfinityTriangleHomotopy (s : SpaceInfinity.{u} _⦋2⦌) :
    SSet.Homotopy (coherentEdgeHom (SpaceInfinity.δ 1 s))
      (coherentEdgeHom (SpaceInfinity.δ 2 s) ≫ coherentEdgeHom (SpaceInfinity.δ 0 s)) :=
  simplicialHomotopyOfFunctorEdge (spaceInfinityTriangleEdge s).toTruncated

/-- 概要：読み戻した円柱は元の精密化の一単体の uncurry そのもの。
方針：定義を展開。規約：代表の選択なし。使われ方：指定 path との比較。 -/
lemma spaceInfinityTriangleHomotopy_h (s : SpaceInfinity.{u} _⦋2⦌) :
    (spaceInfinityTriangleHomotopy s).h =
      uncurry (SSet.yonedaEquiv.symm (coherentTriangleHomotopy s)) := rfl

/-- 概要：指定ホモトピーを辺に戻すと元の精密化の辺そのもの。
方針：Yoneda と curry の往復。規約：類だけに弱めない。使われ方：四面の合成則。 -/
lemma spaceInfinityTriangleHomotopy_edge (s : SpaceInfinity.{u} _⦋2⦌) :
    functorEdgeOfSimplicialHomotopy (spaceInfinityTriangleHomotopy s) =
      (spaceInfinityTriangleEdge s).toTruncated := by
  apply SSet.Truncated.Edge.ext
  change SSet.yonedaEquiv (curry (uncurry
    (SSet.yonedaEquiv.symm (coherentTriangleHomotopy s)))) = coherentTriangleHomotopy s
  rw [curry_uncurry, Equiv.apply_symm_apply]

end SerrePositivity.InfinityCategories.F2
