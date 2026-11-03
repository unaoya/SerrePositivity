module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.DiagonalFiberSourceIsoPrecomp

/-!
概要：元の始点同型の輸送は、元の入力同型の表示変更を保つ。
方針：始点二射の明示的等式を消去し、指定値を同じ型へ戻す。
規約：指定同型を選び直さない。使われ方：四辺比較の制限後の始点輸送。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 元の始点二射と指定同型の表示だけを変えても、指定輸送像の値は保持される。 -/
lemma diagonalFiberTransport_sourceIso_heq_of_heq {E B P : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] {a b : B _⦋0⦌}
    {f g f' g' : P ⟶ vertexFiber p a} (e : FunctorIso f g) (e' : FunctorIso f' g')
    (hf : f = f') (hg : g = g') (he : HEq e e') (c : P ⟶ intervalMappingSpace a b) :
    HEq (diagonalFiberTransport_sourceIso p e c)
      (diagonalFiberTransport_sourceIso p e' c) := by
  subst f' g'
  cases eq_of_heq he
  rfl

/-- 指定輸送像の制限は、同じ制限後の入力同型の表示で保持される。 -/
lemma diagonalFiberTransport_sourceIso_precomp_heq_of_input {E B P Q : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] {a b : B _⦋0⦌}
    {f g : P ⟶ vertexFiber p a} (e : FunctorIso f g)
    (c : P ⟶ intervalMappingSpace a b) (q : Q ⟶ P)
    {f' g' : Q ⟶ vertexFiber p a} (e' : FunctorIso f' g')
    (hf : q ≫ f = f') (hg : q ≫ g = g') (he : HEq (e.precomp q) e') :
    HEq ((diagonalFiberTransport_sourceIso p e c).precomp q)
      (diagonalFiberTransport_sourceIso p e' (q ≫ c)) :=
  (diagonalFiberTransport_sourceIso_precomp_heq p e c q).trans
    (diagonalFiberTransport_sourceIso_heq_of_heq p (e.precomp q) e' hf hg he (q ≫ c))

end SerrePositivity.InfinityCategories.F2
