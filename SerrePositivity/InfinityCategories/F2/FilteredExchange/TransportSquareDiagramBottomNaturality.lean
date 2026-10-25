module

public import
SerrePositivity.InfinityCategories.F2.FilteredExchange.TransportSquareDiagramEndpointComparison
public import
SerrePositivity.InfinityCategories.F2.FilteredExchange.RelativeExtensionIntervalEndpointPresentation

/-!
概要：左下角だけを固定する二実四角形の下辺の、元の指定比較の自然性。
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
lemma TransportSquareDiagram.bottomComparison_naturality :
    D.bottomRightIso M ≪≫ M.bottomComparison = D.bottomComparison := by
  let r := prismEndpoint 0 (Δ[1] ⊗ P)
  have ha : (prismEndpoint 0 P ≫ r) ≫ s.square = SSet.const a := by
    rw [Category.assoc, s.zero, intervalMappingUncurry_zero]
  have hb : (prismEndpoint 1 P ≫ r) ≫ s.square = SSet.const b := by
    rw [Category.assoc, s.zero, intervalMappingUncurry_one]
  have hs : (prismEndpoint 0 P ≫ r) ≫ D.square = f ≫ vertexFiberι p a := by
    exact D.origin
  have hs' : (prismEndpoint 0 P ≫ r) ≫ M.square = f ≫ vertexFiberι p a := by
    exact M.origin
  have he : (prismEndpoint 1 P ≫ r) ≫ D.square = D.bottomRight ≫ vertexFiberι p b := by
    exact D.bottomRight_eq
  have he' : (prismEndpoint 1 P ≫ r) ≫ M.square = M.bottomRight ≫ vertexFiberι p b := by
    exact M.bottomRight_eq
  exact relativeExtensionInterval_source_square_of_initial_at_endpoint p s.square
    (prismEndpoint 0 P ≫ prismEndpoint 0 _) (transportSquareOrigin_leftAnodyne P)
    (f ≫ vertexFiberι p a) transportSquareOrigin_base
    D.square M.square D.over_base M.over_base D.origin M.origin
    r a b ha hb f D.bottomRight M.bottomRight hs hs' he he' s.bottom s.zero
    (𝟙 P) (by rw [Category.id_comp]) (prismEndpoint 1 P ≫ prismEndpoint 0 _) rfl
    transportSquareBottomRight_base D.bottomRight_eq M.bottomRight_eq

end SerrePositivity.InfinityCategories.F2
