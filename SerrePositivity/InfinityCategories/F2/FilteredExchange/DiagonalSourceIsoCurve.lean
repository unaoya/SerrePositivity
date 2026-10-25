module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.DiagonalFiberSourceIsoInput

/-!
概要：元の指定始点同型と区間族の表示を同時に変えても、同じ sourceIso の値を保持。
方針：始点二射と区間の明示的等式を消去する。
規約：指定同型を選び直さない。使われ方：元の Kan 合成四角形の辺表示。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 元の入力同型と区間の表示変更は、元の指定 sourceIso の値を保持する。 -/
lemma diagonalFiberTransport_sourceIso_heq_of_data {E B P : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] {a b : B _⦋0⦌}
    {f g f' g' : P ⟶ vertexFiber p a} (e : FunctorIso f g) (e' : FunctorIso f' g')
    (c c' : P ⟶ intervalMappingSpace a b) (hf : f = f') (hg : g = g')
    (he : HEq e e') (hc : c = c') :
    HEq (diagonalFiberTransport_sourceIso p e c)
      (diagonalFiberTransport_sourceIso p e' c') := by
  cases hc
  exact diagonalFiberTransport_sourceIso_heq_of_heq p e e' hf hg he c

end SerrePositivity.InfinityCategories.F2
