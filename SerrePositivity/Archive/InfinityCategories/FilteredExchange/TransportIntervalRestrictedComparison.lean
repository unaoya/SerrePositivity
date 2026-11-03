module

public import
SerrePositivity.Archive.InfinityCategories.FilteredExchange.TransportIntervalComparisonPrecomp
public import
SerrePositivity.Archive.InfinityCategories.FilteredExchange.TransportIntervalUniversalIdentity

/-!
概要：係数を制限した元の指定区間比較を、同じ実制限 prism の別表示へ戻す。
方針：全係数の自然性の後に、実 prism の等式を適用する。
規約：元の指定比較を保持。使われ方：実四角形の四辺の同時係数制限。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 元の比較の制限は、同じ制限 prism を明示した元の区間比較の値を保つ。 -/
lemma leftFibrationPrism_transportIntervalIso_precomp_heq_of_prism {E B P Q : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] {a b : B _⦋0⦌}
    (f : P ⟶ vertexFiber p a) (g : P ⟶ vertexFiber p b)
    (c : P ⟶ intervalMappingSpace a b) (W : Δ[1] ⊗ P ⟶ E)
    (hs : prismEndpoint 0 P ≫ W = f ≫ vertexFiberι p a)
    (he : prismEndpoint 1 P ≫ W = g ≫ vertexFiberι p b)
    (hp : W ≫ p = intervalMappingUncurry c) (q : Q ⟶ P) (W' : Δ[1] ⊗ Q ⟶ E)
    (hs' : prismEndpoint 0 Q ≫ W' = (q ≫ f) ≫ vertexFiberι p a)
    (he' : prismEndpoint 1 Q ≫ W' = (q ≫ g) ≫ vertexFiberι p b)
    (hp' : W' ≫ p = intervalMappingUncurry (q ≫ c)) (hW : (Δ[1] ◁ q) ≫ W = W') :
    HEq ((leftFibrationPrism_transportIntervalIso p f g c W hs he hp).precomp q)
      (leftFibrationPrism_transportIntervalIso p (q ≫ f) (q ≫ g) (q ≫ c) W' hs' he' hp') := by
  have hs₀ : prismEndpoint 0 Q ≫ ((Δ[1] ◁ q) ≫ W) = (q ≫ f) ≫ vertexFiberι p a := by
    rw [← Category.assoc, prismEndpoint_naturality, Category.assoc, hs, Category.assoc]
  have he₀ : prismEndpoint 1 Q ≫ ((Δ[1] ◁ q) ≫ W) = (q ≫ g) ≫ vertexFiberι p b := by
    rw [← Category.assoc, prismEndpoint_naturality, Category.assoc, he, Category.assoc]
  have hp₀ : ((Δ[1] ◁ q) ≫ W) ≫ p = intervalMappingUncurry (q ≫ c) := by
    rw [Category.assoc, hp, intervalMappingUncurry_precomp]
  exact (leftFibrationPrism_transportIntervalIso_precomp_heq p f g c W hs he hp q
    hs₀ he₀ hp₀).trans (heq_of_eq
      (leftFibrationPrism_transportIntervalIso_eq_of_prism_eq p (q ≫ f) (q ≫ g) (q ≫ c)
        ((Δ[1] ◁ q) ≫ W) W' hs₀ hs' he₀ he' hp₀ hp' hW))

end SerrePositivity.InfinityCategories.F2
