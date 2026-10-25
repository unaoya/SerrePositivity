module

public import
SerrePositivity.InfinityCategories.F2.FilteredExchange.TransportSquareLiftEndpointComparison
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.RelativeExtensionIntervalSourceSquare

/-!
概要：同じ底辺を固定する二四角形の上辺比較は、元の上二頂点像に自然。
方針：同じ全延長比較の上辺制限に、元の区間表示の指定自然性を適用する。
規約：元の三つの指定比較を保持。使われ方：全四角形の比較値の選択独立性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {E B P : SSet.{u}} {p : E ⟶ B} [LeftFibration p]
  {a b c d : B _⦋0⦌} {s : TransportIntervalSquare P a b c d}
  {f : P ⟶ vertexFiber p a} (L M : TransportSquareLift p s f)

/-- 元の上辺の指定比較は、全延長比較の同じ上二頂点像の正方形を満たす。 -/
lemma TransportSquareLift.topComparison_naturality :
    L.topRightIso M ≪≫ M.topComparison = L.topComparison ≪≫
      diagonalFiberTransport_sourceIso p (L.topLeftIso M) s.top := by
  let r := prismEndpoint 1 (Δ[1] ⊗ P)
  have ha : (prismEndpoint 0 P ≫ r) ≫ s.square = SSet.const c := transportSquareTopLeft_base
  have hb : (prismEndpoint 1 P ≫ r) ≫ s.square = SSet.const d := transportSquareTopRight_base
  have hs : (prismEndpoint 0 P ≫ r) ≫ L.square = L.topLeft ≫ vertexFiberι p c := by
    rw [Category.assoc]; exact L.topLeft_ι.symm
  have hs' : (prismEndpoint 0 P ≫ r) ≫ M.square = M.topLeft ≫ vertexFiberι p c := by
    rw [Category.assoc]; exact M.topLeft_ι.symm
  have he : (prismEndpoint 1 P ≫ r) ≫ L.square = L.topRight ≫ vertexFiberι p d := by
    rw [Category.assoc]; exact L.topRight_ι.symm
  have he' : (prismEndpoint 1 P ≫ r) ≫ M.square = M.topRight ≫ vertexFiberι p d := by
    rw [Category.assoc]; exact M.topRight_ι.symm
  exact relativeExtensionInterval_source_square p s.square (prismEndpoint 0 _)
    (prismEndpoint_zero_leftAnodyne _) (diagonalUniversalPrism p f s.bottom)
    transportSquareBottom_base L.square M.square L.over_base M.over_base L.zero M.zero
    r c d ha hb L.topLeft M.topLeft L.topRight M.topRight hs hs' he he' s.top s.one

end SerrePositivity.InfinityCategories.F2
