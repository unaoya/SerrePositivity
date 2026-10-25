module

public import
SerrePositivity.InfinityCategories.F2.FilteredExchange.TransportSquareComparisonPrecomp

/-!
概要：元の選択済み transportIso は、全係数を制限しても元の指定値を保つ。
方針：同じ選択済み実四角形を制限し、任意実面の比較値の同定を両側で使う。
規約：transportIso の選択を保持。使われ方：元の合成比較の全パラメータ自然性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 元の指定四角形比較の全係数制限は、制限後の元の指定四角形比較と値まで一致する。 -/
lemma transportIntervalSquare_transportIso_precomp_heq {E B P Q : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] {a b c d : B _⦋0⦌}
    (s : TransportIntervalSquare P a b c d) (f : P ⟶ vertexFiber p a) (q : Q ⟶ P) :
    HEq ((s.transportIso p f).precomp q) ((s.precomp q).transportIso p (q ≫ f)) := by
  let D := (transportSquareCanonicalLift p s f).diagram
  have h := D.comparison_precomp_heq q
  rw [D.comparison_eq_transportIso, (D.precomp q).comparison_eq_transportIso] at h
  exact h

end SerrePositivity.InfinityCategories.F2
