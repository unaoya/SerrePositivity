module

public import
SerrePositivity.Archive.InfinityCategories.FilteredExchange.TransportSquareDiagramEndpointComparison
public import
SerrePositivity.Archive.InfinityCategories.FilteredExchange.RelativeExtensionIntervalEndpointSquare

/-!
概要：左下角だけを固定する二実四角形の右辺の、元の指定比較の自然性。
方針：元の全延長正方形を、同じ実二頂点の厳密な表示で読む。
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
lemma TransportSquareDiagram.rightComparison_naturality :
    D.topRightIso M ≪≫ M.rightComparison = D.rightComparison ≪≫
      diagonalFiberTransport_sourceIso p (D.bottomRightIso M) s.right := by
  let r := (Δ[1] : SSet.{u}) ◁ prismEndpoint 1 P
  have ha : (prismEndpoint 0 P ≫ r) ≫ s.square = SSet.const b := by
    rw [Category.assoc, s.inner_one, intervalMappingUncurry_zero]
  have hb : (prismEndpoint 1 P ≫ r) ≫ s.square = SSet.const d := by
    rw [Category.assoc, s.inner_one, intervalMappingUncurry_one]
  have hs : (prismEndpoint 0 P ≫ r) ≫ D.square = D.bottomRight ≫ vertexFiberι p b := by
    rw [prismEndpoint_square_exchange]; exact D.bottomRight_eq
  have hs' : (prismEndpoint 0 P ≫ r) ≫ M.square = M.bottomRight ≫ vertexFiberι p b := by
    rw [prismEndpoint_square_exchange]; exact M.bottomRight_eq
  have he : (prismEndpoint 1 P ≫ r) ≫ D.square = D.topRight ≫ vertexFiberι p d := by
    rw [prismEndpoint_square_exchange]; exact D.topRight_eq
  have he' : (prismEndpoint 1 P ≫ r) ≫ M.square = M.topRight ≫ vertexFiberι p d := by
    rw [prismEndpoint_square_exchange]; exact M.topRight_eq
  exact relativeExtensionInterval_source_square_at_endpoints p s.square
    (prismEndpoint 0 P ≫ prismEndpoint 0 _) (transportSquareOrigin_leftAnodyne P)
    (f ≫ vertexFiberι p a) transportSquareOrigin_base
    D.square M.square D.over_base M.over_base D.origin M.origin
    r b d ha hb D.bottomRight M.bottomRight D.topRight M.topRight
    hs hs' he he' s.right s.inner_one
    (prismEndpoint 1 P ≫ prismEndpoint 0 _) (prismEndpoint 1 P ≫ prismEndpoint 1 _)
    (prismEndpoint_square_exchange 0 1 P) (prismEndpoint_square_exchange 1 1 P)
    transportSquareBottomRight_base transportSquareTopRight_base
    D.bottomRight_eq M.bottomRight_eq D.topRight_eq M.topRight_eq

end SerrePositivity.InfinityCategories.F2
