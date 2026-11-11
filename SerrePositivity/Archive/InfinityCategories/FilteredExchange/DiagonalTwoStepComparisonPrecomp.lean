module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.DiagonalFiberSourceIsoInput
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.VertexIsoCompositionTransport
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.RelativeHomCosliceKanAction

/-!
概要：実二辺の指定比較を貼った値は、元の全係数制限を保つ。
方針：元の始点輸送像の自然性と、二段対角輸送の端点の等式を使う。
規約：二つの指定比較を保持。使われ方：四角形の二経路の同時制限。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 同じ二段対角輸送の係数制限は、元の二つの区間を同時に制限したもの。 -/
lemma diagonalFiberTransport_precomp_two {E B P Q : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] {a b c : B _⦋0⦌}
    (f : P ⟶ vertexFiber p a) (l : P ⟶ intervalMappingSpace a b)
    (r : P ⟶ intervalMappingSpace b c) (q : Q ⟶ P) :
    q ≫ diagonalFiberTransport p (diagonalFiberTransport p f l) r =
      diagonalFiberTransport p (diagonalFiberTransport p (q ≫ f) (q ≫ l)) (q ≫ r) := by
  rw [diagonalFiberTransport_precomp, diagonalFiberTransport_precomp]

/-- 元の実二辺比較を貼った指定値は、同じ制限後の二比較を貼った値を保つ。 -/
lemma diagonalTwoStepComparison_precomp_heq {E B P Q : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] {a b c : B _⦋0⦌}
    (f : P ⟶ vertexFiber p a) (g : P ⟶ vertexFiber p b) (h : P ⟶ vertexFiber p c)
    (l : P ⟶ intervalMappingSpace a b) (r : P ⟶ intervalMappingSpace b c)
    (e₀ : FunctorIso g (diagonalFiberTransport p f l))
    (e₁ : FunctorIso h (diagonalFiberTransport p g r)) (q : Q ⟶ P)
    (e₀' : FunctorIso (q ≫ g) (diagonalFiberTransport p (q ≫ f) (q ≫ l)))
    (e₁' : FunctorIso (q ≫ h) (diagonalFiberTransport p (q ≫ g) (q ≫ r)))
    (h₀ : HEq (e₀.precomp q) e₀') (h₁ : HEq (e₁.precomp q) e₁') :
    HEq (FunctorIso.precomp (e₁ ≪≫ diagonalFiberTransport_sourceIso p e₀ r) q)
      (e₁' ≪≫ diagonalFiberTransport_sourceIso p e₀' (q ≫ r)) := by
  have hsrc := diagonalFiberTransport_sourceIso_precomp_heq_of_input p e₀ r q e₀' rfl
    (diagonalFiberTransport_precomp p f l q) h₀
  rw [functorIso_precomp_trans]
  exact vertexIso_trans_heq_of_heq _ _ _ _ rfl
    (congrArg functorVertex (diagonalFiberTransport_precomp p g r q))
    (congrArg functorVertex (diagonalFiberTransport_precomp_two p f l r q)) h₁ hsrc

end SerrePositivity.InfinityCategories.F2
