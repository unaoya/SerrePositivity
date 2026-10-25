module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.TransportTriangleDiagram
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.TransportIntervalSharedPrism

/-!
概要：同じ実辺を共有する二つの実三角形では、対応する指定比較の値が一致する。
方針：抽象的な実三角形上で表示変更を消去してから、実面へ特殊化する。
規約：比較の値を再選択しない。使われ方：四面体の共有辺の比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {E B P : SSet.{u}} {p : E ⟶ B} [LeftFibration p]
  {a b c a' b' c' : B _⦋0⦌}

/-- 二つの実三角形の同じ実bottom辺では、元の指定比較も同じ値。 -/
lemma transportTriangle_bottomComparison_shared_heq
    {s : TransportIntervalSquare P a b c c} {t : TransportIntervalSquare P a b c' c'}
    {f : P ⟶ vertexFiber p a} {g : P ⟶ vertexFiber p b}
    {h : P ⟶ vertexFiber p c} {h' : P ⟶ vertexFiber p c'}
    (T : TransportTriangleDiagram p s f g h) (U : TransportTriangleDiagram p t f g h')
    (hW : T.diagram.bottomPrism = U.diagram.bottomPrism) :
    HEq T.diagram.bottomComparison U.diagram.bottomComparison := by
  unfold TransportSquareDiagram.bottomComparison
  exact leftFibrationPrism_transportIntervalIso_shared_prism_heq
    p _ _ _ _ _ _ _ _ _ _ _ _ hW

/-- 二つの実三角形の同じ実left辺では、元の指定比較も同じ値。 -/
lemma transportTriangle_leftComparison_shared_heq
    {s : TransportIntervalSquare P a b c c} {t : TransportIntervalSquare P a b' c c}
    {f : P ⟶ vertexFiber p a} {g : P ⟶ vertexFiber p b}
    {g' : P ⟶ vertexFiber p b'} {h : P ⟶ vertexFiber p c}
    (T : TransportTriangleDiagram p s f g h) (U : TransportTriangleDiagram p t f g' h)
    (hW : T.diagram.leftPrism = U.diagram.leftPrism) :
    HEq T.diagram.leftComparison U.diagram.leftComparison := by
  unfold TransportSquareDiagram.leftComparison
  exact leftFibrationPrism_transportIntervalIso_shared_prism_heq
    p _ _ _ _ _ _ _ _ _ _ _ _ hW

/-- 二つの実三角形の同じ実right辺では、元の指定比較も同じ値。 -/
lemma transportTriangle_rightComparison_shared_heq
    {s : TransportIntervalSquare P a b c c} {t : TransportIntervalSquare P a' b c c}
    {f : P ⟶ vertexFiber p a} {f' : P ⟶ vertexFiber p a'}
    {g : P ⟶ vertexFiber p b} {h : P ⟶ vertexFiber p c}
    (T : TransportTriangleDiagram p s f g h) (U : TransportTriangleDiagram p t f' g h)
    (hW : T.diagram.rightPrism = U.diagram.rightPrism) :
    HEq T.diagram.rightComparison U.diagram.rightComparison := by
  unfold TransportSquareDiagram.rightComparison
  exact leftFibrationPrism_transportIntervalIso_shared_prism_heq
    p _ _ _ _ _ _ _ _ _ _ _ _ hW

end SerrePositivity.InfinityCategories.F2
