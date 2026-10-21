module

public import SerrePositivity.InfinityCategories.F1.CocartesianBaseChangeAssociativityEvaluation
public import SerrePositivity.InfinityCategories.F1.CocartesianStrictTransportBaseChangeAction

/-!
概要：同じ結合同型は、元の全相対 Hom の底変換後の section 作用と厳密に可換。
方針：元の全空間へ戻し、任意の次数の同じ射影と評価を照合する。
規約：二重底変換と直接の底変換の元の全高次 Hom の作用を使う。
使われ方：底全体と全 fibration に自然な結合比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory SSet
namespace SerrePositivity.InfinityCategories

/-- 元の全相対 Hom の作用と、底変換の同じ結合同型は全パラメーターで可換。 -/
lemma cocartesianBaseChangeAssociativityComponent_action
    {A D C : Type u} [Category.{u} A] [Category.{u} D] [Category.{u} C] {E F : SSet.{u}}
    (p : E ⟶ nerve C) [CocartesianFibration p] (q : F ⟶ nerve C) [CocartesianFibration q]
    (l : A ⥤ D) (k : D ⥤ C) (a : A) :
    (𝟙 (kanCocartesianStrictTransport
        (pullback.fst (nerveMap l) (pullback.fst (nerveMap k) p)) a) ⊗ₘ
      (cocartesianPullbackNativeRestriction p q (Over.mk (nerveMap k)) ≫
        cocartesianPullbackNativeRestriction (pullback.fst (nerveMap k) p)
          (pullback.fst (nerveMap k) q) (Over.mk (nerveMap l)))) ≫
      cocartesianSectionsAction (Over.mk (nerveMap (Under.forget a)))
        (Over.mk (pullback.fst (nerveMap l) (pullback.fst (nerveMap k) p)))
        (Over.mk (pullback.fst (nerveMap l) (pullback.fst (nerveMap k) q))) ≫
        (cocartesianBaseChangeAssociativityComponent q l k a).hom =
    ((cocartesianBaseChangeAssociativityComponent p l k a).hom ⊗ₘ
      cocartesianPullbackNativeRestriction p q (Over.mk (nerveMap (l ⋙ k)))) ≫
      cocartesianSectionsAction (Over.mk (nerveMap (Under.forget a)))
        (Over.mk (pullback.fst (nerveMap (l ⋙ k)) p))
        (Over.mk (pullback.fst (nerveMap (l ⋙ k)) q)) := by
  apply (cancel_mono (cocartesianSectionsPullbackIso
    (IsPullback.of_hasPullback (nerveMap (l ⋙ k)) q).flip
    (nerveMap (Under.forget a)) (nerveMap (Under.forget a) ≫ nerveMap (l ⋙ k)) rfl).hom).mp
  simp only [Category.assoc, cocartesianBaseChangeAssociativityComponent_iso]
  apply (cancel_mono (kanCocartesianSectionsι q
    (nerveMap (Under.forget a) ≫ nerveMap (l ⋙ k)))).mp
  apply relativeFunctorUncurry_injective q (nerveMap (Under.forget a) ≫ nerveMap (l ⋙ k))
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  rintro ⟨x, s, h⟩
  have hl := cocartesianPullbackNativeRestriction_apply_snd (pullback.fst (nerveMap k) p)
    (pullback.fst (nerveMap k) q) (Over.mk (nerveMap l))
    ((cocartesianPullbackNativeRestriction p q (Over.mk (nerveMap k))).app n h)
    (s.val.val.app n (𝟙 n) x)
  have hk := cocartesianPullbackNativeRestriction_apply_snd p q (Over.mk (nerveMap k)) h
    ((pullback.snd (nerveMap l) (pullback.fst (nerveMap k) p)).app n
      (s.val.val.app n (𝟙 n) x))
  have hd := cocartesianPullbackNativeRestriction_apply_snd p q
    (Over.mk (nerveMap (l ⋙ k))) h
    ((((cocartesianBaseChangeAssociativityComponent p l k a).hom.app n s).val.val.app
      n (𝟙 n)) x)
  have hs := cocartesianBaseChangeAssociativityComponent_apply_snd p l k a s x
  exact ((congrArg ((pullback.snd (nerveMap k) q).app n) hl).trans hk).trans
    (hd.trans (congrArg (fun y ↦ h.val.val.app n (𝟙 n) y) hs)).symm

end SerrePositivity.InfinityCategories
