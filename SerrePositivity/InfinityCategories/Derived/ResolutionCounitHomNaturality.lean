module
public import SerrePositivity.InfinityCategories.Derived.FunctorHomPostcompIdentity
public import SerrePositivity.InfinityCategories.Derived.ResolutionCounitComparison
/-!
概要：指定余単位と完全充満性による元の入力比較の、任意全関手射自然性。
方針：全関手空間の交換則から同じ指定比較の正方形を得て、忠実性で反映する。
規約：比較を選び直さず、射の可逆性を要求しない。使われ方：分解変更の自然性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet MonoidalClosed
lemma resolutionCounitComparison_hom_naturality
    {A B : SSet.{u}} [Quasicategory A] [Quasicategory B]
    {f : A ⟶ A} {g : B ⟶ B}
    (e : FunctorIso f (𝟙 A)) (d : FunctorIso g (𝟙 B))
    {h k : A ⟶ B} (a : FunctorHom h k) :
    (resolutionCounitComparison e d h).hom ≫ functorHomPostcomp h k g a =
      functorHomPrecomp h k f a ≫ (resolutionCounitComparison e d k).hom := by
  have he := functorHom_whisker_exchange_typed e.hom a
  have hd := functorHom_whisker_exchange_typed a d.inv
  have hi : functorHomPrecomp h k (𝟙 A) a = a := functorHom_precomp_id a
  rw [hi] at he
  rw [functorHom_postcomp_id] at hd
  simp only [resolutionCounitComparison, Iso.trans_hom, Iso.symm_hom,
    functorIso_postcomp_hom_typed]
  calc
    _ = functorHomPostcomp f (𝟙 A) h e.hom ≫
        (functorHomPrecomp (𝟙 B) g h d.inv ≫ functorHomPostcomp h k g a) :=
      Category.assoc _ _ _
    _ = functorHomPostcomp f (𝟙 A) h e.hom ≫
        (a ≫ functorHomPrecomp (𝟙 B) g k d.inv) := congrArg (fun z => _ ≫ z) hd.symm
    _ = (functorHomPostcomp f (𝟙 A) h e.hom ≫ a) ≫
        functorHomPrecomp (𝟙 B) g k d.inv := (Category.assoc _ _ _).symm
    _ = (functorHomPrecomp h k f a ≫ functorHomPostcomp f (𝟙 A) k e.hom) ≫
        functorHomPrecomp (𝟙 B) g k d.inv := congrArg (fun z => z ≫ _) he
    _ = _ := Category.assoc _ _ _
end SerrePositivity.InfinityCategories
