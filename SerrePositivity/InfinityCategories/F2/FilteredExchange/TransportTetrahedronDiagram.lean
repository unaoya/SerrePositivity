module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.TransportTetrahedronFace
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.TransportTriangleSimplexEdges
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.SimplexSharedFacePrism

/-!
概要：一つの実四面体とその元の四頂点をまとめて保持する。
方針：四面を同じ実全図式の制限から取り出す。
規約：面や合成比較の整合性を仮定に加えない。使われ方：指定比較の四面体則。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 同じ実四面体の四頂点を、元の fiber の値として保持する。 -/
structure TransportTetrahedronDiagram {E B P : SSet.{u}} (p : E ⟶ B)
    (v : Fin 4 → B _⦋0⦌) (f : ∀ i, P ⟶ vertexFiber p (v i)) where
  /-- 実全四面体。 -/
  simplex : (Δ[3] : SSet.{u}) ⊗ P ⟶ E
  /-- 四つの元の実頂点。 -/
  vertex_eq : ∀ i, simplexPrismVertex 3 i P ≫ simplex = f i ≫ vertexFiberι p (v i)

variable {E B P : SSet.{u}} {p : E ⟶ B} {v : Fin 4 → B _⦋0⦌}
  {f : ∀ i, P ⟶ vertexFiber p (v i)} (D : TransportTetrahedronDiagram p v f)

/-- 元の実四面体の面を、元の三頂点と実三辺を持つ輸送三角形として読む。 -/
def TransportTetrahedronDiagram.face (k : Fin 4) :=
  transportTetrahedronFaceOfSimplex p D.simplex k
    (f (k.succAbove 0)) (f (k.succAbove 1)) (f (k.succAbove 2))
    (D.vertex_eq _) (D.vertex_eq _) (D.vertex_eq _)

/-- 面の第一辺は元の実四面体の二重面そのもの。 -/
lemma TransportTetrahedronDiagram.face_bottomPrism (k : Fin 4) :
    (D.face k).diagram.bottomPrism =
      (stdSimplex.δ (2 : Fin 3) ▷ P) ≫ ((stdSimplex.δ k ▷ P) ≫ D.simplex) :=
  transportTriangleSimplex_bottomPrism _ _ _ _ _ _ _ _

/-- 面の長辺は元の実四面体の二重面そのもの。 -/
lemma TransportTetrahedronDiagram.face_leftPrism (k : Fin 4) :
    (D.face k).diagram.leftPrism =
      (stdSimplex.δ (1 : Fin 3) ▷ P) ≫ ((stdSimplex.δ k ▷ P) ≫ D.simplex) :=
  transportTriangleSimplex_leftPrism _ _ _ _ _ _ _ _

/-- 面の最後辺は元の実四面体の二重面そのもの。 -/
lemma TransportTetrahedronDiagram.face_rightPrism (k : Fin 4) :
    (D.face k).diagram.rightPrism =
      (stdSimplex.δ (0 : Fin 3) ▷ P) ≫ ((stdSimplex.δ k ▷ P) ≫ D.simplex) :=
  transportTriangleSimplex_rightPrism _ _ _ _ _ _ _ _

end SerrePositivity.InfinityCategories.F2
