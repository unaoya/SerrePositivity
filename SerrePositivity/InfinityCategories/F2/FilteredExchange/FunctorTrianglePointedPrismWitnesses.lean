module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.FunctorTrianglePointedEndpoints
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.RelativeExtensionEndpointWitness

/-!
概要：元の全三角形の同じ三辺を、実始域・実終点を保つ三つの prism 証拠へ移す。
方針：元の面式と全中間頂点・全終点の二射影を使う。
規約：三辺を選び直さない。使われ方：右辺比較の自然性と三角形の指定比較の式。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {B C : SSet.{u + 1}} {F G J : B ⟶ SpaceInfinity.{u}}
  {a : SSet.Homotopy F G} {b : SSet.Homotopy G J} {c : SSet.Homotopy F J}
  {T : FunctorCompositionTriangle a b c} {p : C ⟶ B} {s : C ⟶ leftUnstraightening F}
  (w : FunctorTrianglePointedWitness T p s)

/-- 元の同じ第一辺の実 prism と実中間頂点を保持する証拠。 -/
def FunctorTrianglePointedWitness.firstWitness :
    RelativeExtensionEndpointWitness pointedSpaceProjection
      ((Δ[1] ◁ p) ≫ functorSimplexDiagram (curry a.h)) (prismEndpoint 0 C)
      (s ≫ pullback.fst pointedSpaceProjection F) (prismEndpoint 1 C) G p where
  extension := (stdSimplex.δ (2 : Fin 3) ▷ C) ≫ w.prism
  over := by
    rw [Category.assoc, w.projection]
    exact functorTrianglePrism_edge_base T.diagram p 2 a T.face_two
  initial := w.initial
  endpoint := w.middle
  endpoint_over := w.middle_projection
  evaluate := w.middle_pointed

/-- 元の同じ右辺は、元の実中間頂点を始点、元の実終点を終点とする証拠。 -/
def FunctorTrianglePointedWitness.secondWitness :
    RelativeExtensionEndpointWitness pointedSpaceProjection
      ((Δ[1] ◁ p) ≫ functorSimplexDiagram (curry b.h)) (prismEndpoint 0 C)
      (w.middle ≫ pullback.fst pointedSpaceProjection G) (prismEndpoint 1 C) J p where
  extension := (stdSimplex.δ (0 : Fin 3) ▷ C) ≫ w.prism
  over := by
    rw [Category.assoc, w.projection]
    exact functorTrianglePrism_edge_base T.diagram p 0 b T.face_zero
  initial := w.middle_pointed
  endpoint := w.endpoint
  endpoint_over := w.endpoint_projection
  evaluate := w.endpoint_pointed

/-- 元の同じ長辺は、元の実始域射と実終点を同時に保持する証拠。 -/
def FunctorTrianglePointedWitness.longWitness :
    RelativeExtensionEndpointWitness pointedSpaceProjection
      ((Δ[1] ◁ p) ≫ functorSimplexDiagram (curry c.h)) (prismEndpoint 0 C)
      (s ≫ pullback.fst pointedSpaceProjection F) (prismEndpoint 1 C) J p where
  extension := (stdSimplex.δ (1 : Fin 3) ▷ C) ≫ w.prism
  over := by
    rw [Category.assoc, w.projection]
    exact functorTrianglePrism_edge_base T.diagram p 1 c T.face_one
  initial := w.initial
  endpoint := w.endpoint
  endpoint_over := w.endpoint_projection
  evaluate := w.endpoint_pointed

end SerrePositivity.InfinityCategories.F2
