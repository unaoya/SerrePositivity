module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.TransportSquareSourceActionIso
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.FunctorIsoComponentNaturality

/-!
概要：元の選択済み四角形比較は、元の始点同型の二段輸送と自然な正方形をなす。
方針：同じ全始点作用の関手同型の自然性を、元の指定値へ全成分で戻す。
規約：係数に quasicategory 性を追加せず、四つの元の指定同型を保持。
使われ方：元の合成四角形の中間始点比較の移動と消去。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
attribute [local instance] vertexFiber_kanComplex_of_leftFibration

/-- 元の四角形比較は、同じ元の始点同型の二つの二段輸送と可換。 -/
lemma transportIntervalSquare_transportIso_source_naturality {E B P : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] {a b c d : B _⦋0⦌}
    (s : TransportIntervalSquare P a b c d) {f g : P ⟶ vertexFiber p a}
    (e : FunctorIso f g) :
    diagonalFiberTransport_sourceIso p (diagonalFiberTransport_sourceIso p e s.bottom) s.right ≪≫
        s.transportIso p g =
      s.transportIso p f ≪≫
        diagonalFiberTransport_sourceIso p (diagonalFiberTransport_sourceIso p e s.left) s.top := by
  have h := functorIso_app_vertexIso_naturality (transportIntervalSquareSourceActionIso p s) e
  exact vertexIso_square_of_heq _ _ _ _ _ _ _ _
    (diagonalTwoStepSourceAction_vertex p f s.bottom s.right)
    (diagonalTwoStepSourceAction_vertex p g s.bottom s.right)
    (diagonalTwoStepSourceAction_vertex p f s.left s.top)
    (diagonalTwoStepSourceAction_vertex p g s.left s.top)
    (diagonalFiberTransport_sourceIso_two_heq_action p e s.bottom s.right).symm
    (transportIntervalSquareSourceActionIso_app_heq p s g)
    (transportIntervalSquareSourceActionIso_app_heq p s f)
    (diagonalFiberTransport_sourceIso_two_heq_action p e s.left s.top).symm h

end SerrePositivity.InfinityCategories.F2
