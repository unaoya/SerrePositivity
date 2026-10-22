module

public import SerrePositivity.InfinityCategories.F2.FunctorSimplexPointedStart

/-!
概要：定値関手族の全 prism の底を、同じ一次単体の係数射影へ厳密に同定する。
方針：curry の往復と直積の交換後の射影を任意の射に対して先に計算する。
規約：元の射と係数を保持。使われ方：元の定値余極限辺の全底の計算。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 同じ一次単体を定値関手族へ写した全 prism の底は、同じ係数射影後の元の射。 -/
lemma functorSimplexDiagram_constant_curry {K B X : SSet.{u}}
    (p : K ⟶ B) (e : (Δ[1] : SSet.{u}) ⟶ X) :
    (Δ[1] ◁ p) ≫ functorSimplexDiagram (curry (snd B Δ[1] ≫ e)) = fst Δ[1] K ≫ e := by
  unfold functorSimplexDiagram
  rw [uncurry_curry]
  have hn : (Δ[1] ◁ p) ≫ (β_ Δ[1] B).hom ≫ snd B Δ[1] = fst Δ[1] K := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro k
    rfl
  simpa only [Category.assoc] using congrArg (fun q => q ≫ e) hn

/-- 定値 curry 表示が与えられた同じ辺の底を、元の一次単体へ戻す。 -/
lemma functorSimplexDiagram_constant_base_of_eq {K B X : SSet.{u}}
    (p : K ⟶ B) (c : Δ[1] ⟶ (ihom B).obj X) (e : Δ[1] ⟶ X)
    (h : c = curry (snd B Δ[1] ≫ e)) :
    (Δ[1] ◁ p) ≫ functorSimplexDiagram (curry (uncurry c)) = fst Δ[1] K ≫ e := by
  rw [curry_uncurry, h]
  exact functorSimplexDiagram_constant_curry p e

end SerrePositivity.InfinityCategories.F2
