module

public import SerrePositivity.EInfinity.Hammock.WordSurjectionComparison
public import SerrePositivity.EInfinity.Hammock.RawHammock

/-!
# 同じ元の全射による未縮約 hammock の比較

概要：元の全射が同じ列の写像を与えるなら、像の語を含む未縮約対象は等しい。
方針：全射の終域の色の回収と、同じ元の graph の遷移を使う。
規約：余極限内の値の一致だけから比較を推論しない。
使われ方：二つの基本合成の共通対象の同定。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.EInfinity.Hammock
open CategoryTheory

lemma raw_eq_of_surjections {C : Type u} [Category.{v} C] (W : MorphismProperty C)
    [W.IsMultiplicative] (X Y : C) {a b c : Word} (f : a ⟶ b) (g : a ⟶ c)
    (hf : Function.Surjective f.orderHom) (hn : b.length = c.length)
    (hfg : ∀ i, Fin.cast hn (f.orderHom i) = g.orderHom i) (n : SimplexCategoryᵒᵖ)
    (τ : (graph W a X Y).obj n) :
    (⟨b, ((graphDiagram W X Y).map f).app n τ⟩ : RawHammock W X Y n) =
      ⟨c, ((graphDiagram W X Y).map g).app n τ⟩ := by
  obtain ⟨hbc, he⟩ := Word.target_eq_of_surjective f g hf hn hfg
  cases hbc
  rw [eqToHom_refl, Category.comp_id] at he
  subst g
  rfl

end SerrePositivity.EInfinity.Hammock
