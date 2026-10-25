module

public import
SerrePositivity.InfinityCategories.F2.FilteredExchange.TransportSquareDiagramEndpointComparison
public import
SerrePositivity.InfinityCategories.F2.FilteredExchange.RelativeExtensionIntervalEndpointSquare

/-!
概要：左下角だけを固定する二実四角形の上辺の、元の指定比較の自然性。
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
lemma TransportSquareDiagram.topComparison_naturality :
    D.topRightIso M ≪≫ M.topComparison = D.topComparison ≪≫
      diagonalFiberTransport_sourceIso p (D.topLeftIso M) s.top := by
  let r := prismEndpoint 1 (Δ[1] ⊗ P)
  have ha : (prismEndpoint 0 P ≫ r) ≫ s.square = SSet.const c := by
    rw [Category.assoc, s.one, intervalMappingUncurry_zero]
  have hb : (prismEndpoint 1 P ≫ r) ≫ s.square = SSet.const d := by
    rw [Category.assoc, s.one, intervalMappingUncurry_one]
  have hs : (prismEndpoint 0 P ≫ r) ≫ D.square = D.topLeft ≫ vertexFiberι p c := by
    exact D.topLeft_eq
  have hs' : (prismEndpoint 0 P ≫ r) ≫ M.square = M.topLeft ≫ vertexFiberι p c := by
    exact M.topLeft_eq
  have he : (prismEndpoint 1 P ≫ r) ≫ D.square = D.topRight ≫ vertexFiberι p d := by
    exact D.topRight_eq
  have he' : (prismEndpoint 1 P ≫ r) ≫ M.square = M.topRight ≫ vertexFiberι p d := by
    exact M.topRight_eq
  exact relativeExtensionInterval_source_square_at_endpoints p s.square
    (prismEndpoint 0 P ≫ prismEndpoint 0 _) (transportSquareOrigin_leftAnodyne P)
    (f ≫ vertexFiberι p a) transportSquareOrigin_base
    D.square M.square D.over_base M.over_base D.origin M.origin
    r c d ha hb D.topLeft M.topLeft D.topRight M.topRight
    hs hs' he he' s.top s.one
    (prismEndpoint 0 P ≫ prismEndpoint 1 _) (prismEndpoint 1 P ≫ prismEndpoint 1 _) rfl rfl
    transportSquareTopLeft_base transportSquareTopRight_base
    D.topLeft_eq M.topLeft_eq D.topRight_eq M.topRight_eq

end SerrePositivity.InfinityCategories.F2
