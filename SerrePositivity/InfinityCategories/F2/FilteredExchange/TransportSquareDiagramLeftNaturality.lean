module

public import
SerrePositivity.InfinityCategories.F2.FilteredExchange.TransportSquareDiagramEndpointComparison
public import
SerrePositivity.InfinityCategories.F2.FilteredExchange.RelativeExtensionIntervalEndpointPresentation

/-!
概要：左下角だけを固定する二実四角形の左辺の、元の指定比較の自然性。
方針：全延長正方形から固定初期値の恒等比較を消去する。
規約：元の四辺比較を保持。使われ方：任意の実面の比較値の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {E B P : SSet.{u}} {p : E ⟶ B} [LeftFibration p] {a b c d : B _⦋0⦌}
  {s : TransportIntervalSquare P a b c d} {f : P ⟶ vertexFiber p a}
  (D M : TransportSquareDiagram p s f)

/-- 左下角だけを固定する元の全延長比較と、指定した同じ実辺比較の自然性。 -/
lemma TransportSquareDiagram.leftComparison_naturality :
    D.topLeftIso M ≪≫ M.leftComparison = D.leftComparison := by
  let r := (Δ[1] : SSet.{u}) ◁ prismEndpoint 0 P
  have ha : (prismEndpoint 0 P ≫ r) ≫ s.square = SSet.const a := by
    rw [Category.assoc, s.inner_zero, intervalMappingUncurry_zero]
  have hb : (prismEndpoint 1 P ≫ r) ≫ s.square = SSet.const c := by
    rw [Category.assoc, s.inner_zero, intervalMappingUncurry_one]
  have hs : (prismEndpoint 0 P ≫ r) ≫ D.square = f ≫ vertexFiberι p a := by
    rw [prismEndpoint_square_exchange]; exact D.origin
  have hs' : (prismEndpoint 0 P ≫ r) ≫ M.square = f ≫ vertexFiberι p a := by
    rw [prismEndpoint_square_exchange]; exact M.origin
  have he : (prismEndpoint 1 P ≫ r) ≫ D.square = D.topLeft ≫ vertexFiberι p c := by
    rw [prismEndpoint_square_exchange]; exact D.topLeft_eq
  have he' : (prismEndpoint 1 P ≫ r) ≫ M.square = M.topLeft ≫ vertexFiberι p c := by
    rw [prismEndpoint_square_exchange]; exact M.topLeft_eq
  exact relativeExtensionInterval_source_square_of_initial_at_endpoint p s.square
    (prismEndpoint 0 P ≫ prismEndpoint 0 _) (transportSquareOrigin_leftAnodyne P)
    (f ≫ vertexFiberι p a) transportSquareOrigin_base
    D.square M.square D.over_base M.over_base D.origin M.origin
    r a c ha hb f D.topLeft M.topLeft hs hs' he he' s.left s.inner_zero
    (𝟙 P) (by rw [Category.id_comp, prismEndpoint_square_exchange])
    (prismEndpoint 0 P ≫ prismEndpoint 1 _) (prismEndpoint_square_exchange 1 0 P)
    transportSquareTopLeft_base D.topLeft_eq M.topLeft_eq

end SerrePositivity.InfinityCategories.F2
