module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.TransportTriangleTopComparison
public import
SerrePositivity.InfinityCategories.F2.FilteredExchange.ConstantTransportSourceNaturality

/-!
概要：元の三角形合成比較は、同じ実三辺の指定比較の貼り合わせで計算できる。
方針：任意実四角形の比較値を使い、同じ定値終辺の二因子を消去する。
規約：三つの元の指定比較を保持。使われ方：共通の高次図式の面の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 元の三角形合成比較は、同じ実二辺の比較の逆と実長辺の比較を貼った値。 -/
lemma TransportTriangleDiagram.constantTopIso_eq {E B P : SSet.{u}}
    {p : E ⟶ B} [LeftFibration p] {a b d : B _⦋0⦌}
    {s : TransportIntervalSquare P a b d d} {f : P ⟶ vertexFiber p a}
    {g : P ⟶ vertexFiber p b} {h : P ⟶ vertexFiber p d}
    (T : TransportTriangleDiagram p s f g h)
    (hs : intervalMappingUncurry s.top = SSet.const d) :
    s.constantTopIso p f hs =
      (T.diagram.rightComparison ≪≫
        diagonalFiberTransport_sourceIso p T.diagram.bottomComparison s.right).symm ≪≫
          T.diagram.leftComparison := by
  have hn := diagonalFiberTransport_constantIso_source_naturality p
    T.diagram.leftComparison s.top hs
  unfold TransportIntervalSquare.constantTopIso
  rw [← T.diagram.comparison_eq_transportIso]
  unfold TransportSquareDiagram.comparison
  simp only [Iso.trans_assoc]
  rw [hn, T.topComparison_eq_constant hs]
  exact congrArg (fun e => (T.diagram.rightComparison ≪≫
    diagonalFiberTransport_sourceIso p T.diagram.bottomComparison s.right).symm ≪≫ e)
    (Iso.symm_self_id_assoc (diagonalFiberTransport_constantIso p h s.top hs)
      T.diagram.leftComparison)

end SerrePositivity.InfinityCategories.F2
