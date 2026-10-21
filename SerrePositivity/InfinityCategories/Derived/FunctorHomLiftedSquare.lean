module
public import SerrePositivity.InfinityCategories.Derived.FunctorHomWhiskerMapTransport
/-!
概要：同じ全関手射の正方形を、厳密な上げ下げを保つ持ち上げへ移送する。
方針：全前後合成の交換則と指定した同じ逆写像の恒等関係を使う。
規約：比較の値と全端点を保持。使われ方：元の実入力分解の自然性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet MonoidalClosed
lemma functorHom_lifted_square_heq
    {X Y A B A' B' : SSet.{u}}
    (H K : X ⟶ Y) (q : X ⟶ A) (s : Y ⟶ B) (f g : A ⟶ B)
    (a : FunctorHom f g) (ε : FunctorHom H K)
    (hs : H ≫ s = q ≫ f) (ks : K ≫ s = q ≫ g)
    (he : HEq (functorHomPostcomp H K s ε) (functorHomPrecomp f g q a))
    (i : A ⟶ A') (j : A' ⟶ A) (v : B ⟶ B') (hij : i ≫ j = 𝟙 A) :
    HEq (functorHomPostcomp H K (s ≫ v) ε)
      (functorHomPrecomp (j ≫ f ≫ v) (j ≫ g ≫ v) (q ≫ i)
        (functorHomPrecomp (f ≫ v) (g ≫ v) j (functorHomPostcomp f g v a))) := by
  have h₀ := (heq_of_eq (functorHomPostcomp_postcomp H K s v ε)).symm
  have h₁ := functorHomPostcomp_heq
    (functorHomPostcomp H K s ε) (functorHomPrecomp f g q a) hs ks he v
  have h₂ := heq_of_eq (functorHomPrecomp_postcomp f g q v a)
  have h₃ := heq_of_eq (functorHomPrecomp_precomp (f ≫ v) (g ≫ v) j (q ≫ i)
    (functorHomPostcomp f g v a))
  have hq : (q ≫ i) ≫ j = q := by rw [Category.assoc, hij, Category.comp_id]
  have h₄ := functorHomPrecomp_heq_of_source_eq (functorHomPostcomp f g v a) hq
  exact h₀.trans (h₁.trans (h₂.trans (h₃.trans h₄).symm))
end SerrePositivity.InfinityCategories
