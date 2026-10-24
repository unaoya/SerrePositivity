module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.BaseChangeAssociativityNaturality

/-!
概要：底変換結合同型の全パラメーターの評価は、元の二重 pullback の射影そのもの。
方針：同じ section 同型の等式を展開し、任意の次数で評価する。
規約：零次元への制限や別の比較の選択は行わない。
使われ方：元の全相対 Hom の作用と結合同型の可換式。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories

variable {A D C : Type u} [Category.{u} A] [Category.{u} D] [Category.{u} C]
  {E : SSet.{u}} (p : E ⟶ nerve C) [CocartesianFibration p] (l : A ⥤ D) (k : D ⥤ C)

/-- 同じ結合同型の展開は、二重 pullback の元の全空間への射影を保持する。 -/
lemma cocartesianBaseChangeAssociativityComponent_uncurry_snd (a : A) {T : SSet.{u}}
    (s : T ⟶ SerrePositivity.InfinityCategories.cocartesianStrictTransport
      (pullback.fst (nerveMap l) (pullback.fst (nerveMap k) p)) a) :
    relativeFunctorUncurry ((s ≫ (cocartesianBaseChangeAssociativityComponent p l k a).hom) ≫
      SerrePositivity.InfinityCategories.cocartesianSectionsι (pullback.fst (nerveMap (l ⋙ k)) p)
        (nerveMap (Under.forget a))) ≫ pullback.snd (nerveMap (l ⋙ k)) p =
    relativeFunctorUncurry (s ≫ SerrePositivity.InfinityCategories.cocartesianSectionsι
      (pullback.fst (nerveMap l) (pullback.fst (nerveMap k) p)) (nerveMap (Under.forget a))) ≫
      pullback.snd (nerveMap l) (pullback.fst (nerveMap k) p) ≫ pullback.snd (nerveMap k) p := by
  have hd := cocartesianSectionsPullbackIso_hom_uncurry
    (IsPullback.of_hasPullback (nerveMap (l ⋙ k)) p).flip
    (nerveMap (Under.forget a)) (nerveMap (Under.forget a) ≫ nerveMap (l ⋙ k)) rfl
    (s ≫ (cocartesianBaseChangeAssociativityComponent p l k a).hom)
  have hc := cocartesianSectionsPullbackIso_hom_uncurry
    (cocartesianBaseChangeComposite_isPullback p l k)
    (nerveMap (Under.forget a)) (nerveMap (Under.forget a) ≫ nerveMap (l ⋙ k)) rfl s
  have ht := congrArg (fun z ↦ relativeFunctorUncurry
    ((s ≫ z) ≫ SerrePositivity.InfinityCategories.cocartesianSectionsι p
      (nerveMap (Under.forget a) ≫ nerveMap (l ⋙ k))))
    (cocartesianBaseChangeAssociativityComponent_iso p l k a)
  simpa only [Category.assoc] using hd.symm.trans (ht.trans hc)

/-- 同じ結合同型の評価は、任意の次数の section の同じ全空間での評価に一致する。 -/
lemma cocartesianBaseChangeAssociativityComponent_apply_snd (a : A)
    {n : SimplexCategoryᵒᵖ}
    (s : (SerrePositivity.InfinityCategories.cocartesianStrictTransport
      (pullback.fst (nerveMap l) (pullback.fst (nerveMap k) p)) a).obj n)
    (x : (nerve (Under a)).obj n) :
    (pullback.snd (nerveMap (l ⋙ k)) p).app n
      ((((cocartesianBaseChangeAssociativityComponent p l k a).hom.app n s).val.val.app
        n (𝟙 n)) x) =
    (pullback.snd (nerveMap k) p).app n
      ((pullback.snd (nerveMap l) (pullback.fst (nerveMap k) p)).app n
        (s.val.val.app n (𝟙 n) x)) := by
  have h := cocartesianBaseChangeAssociativityComponent_uncurry_snd p l k a (𝟙 _)
  exact congrArg (fun z ↦ z.app n (x, s)) h

end SerrePositivity.InfinityCategories
