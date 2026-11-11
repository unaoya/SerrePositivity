module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FunctorIsoPrecompFaithful
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FunctorIsoWhiskerComposition

/-!
概要：値射への像の指定等式を、端点を明示した再制限で移送・反映する。
方針：実端点の等式を消去し、前後合成の交換と前合成の忠実性を使う。
規約：HEq から端点等式を取り出さない。使われ方：元の全三角形の値比較の反映。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2

/-- 実端点を保つ同じ二比較の再制限は、値射への元の指定等式を保持する。 -/
lemma functorIso_value_eq_of_precomp_heq {A X Y Z : SSet.{u}}
    {f g : X ⟶ Y} {f' g' : A ⟶ Y} (e : FunctorIso f g) (V : Y ⟶ Z)
    (b : FunctorIso (f ≫ V) (g ≫ V)) (r : A ⟶ X)
    (e' : FunctorIso f' g') (b' : FunctorIso (f' ≫ V) (g' ≫ V))
    (hf : r ≫ f = f') (hg : r ≫ g = g')
    (he : HEq (e.precomp r) e') (hb : HEq (b.precomp r) b')
    (h : e.postcomp V = b) : e'.postcomp V = b' := by
  subst f' g'
  cases eq_of_heq he
  cases eq_of_heq hb
  rw [functorIso_precomp_postcomp, h]

/-- 同じ再制限が同値なら、値射への元の指定等式を忠実に反映する。 -/
lemma functorIso_value_eq_iff_precomp_heq {A X Y Z : SSet.{u}}
    [Quasicategory A] [Quasicategory X] [Quasicategory Z]
    {f g : X ⟶ Y} {f' g' : A ⟶ Y} (e : FunctorIso f g) (V : Y ⟶ Z)
    (b : FunctorIso (f ≫ V) (g ≫ V)) (r : A ⟶ X) (hr : IsQCatEquivalence r)
    (e' : FunctorIso f' g') (b' : FunctorIso (f' ≫ V) (g' ≫ V))
    (hf : r ≫ f = f') (hg : r ≫ g = g')
    (he : HEq (e.precomp r) e') (hb : HEq (b.precomp r) b') :
    e.postcomp V = b ↔ e'.postcomp V = b' := by
  subst f' g'
  cases eq_of_heq he
  cases eq_of_heq hb
  constructor
  · intro h
    rw [functorIso_precomp_postcomp, h]
  · intro h
    apply functorIso_precomp_injective_of_qCatEquivalence r hr
    change (e.postcomp V).precomp r = b.precomp r
    rw [← functorIso_precomp_postcomp]
    exact h

end SerrePositivity.InfinityCategories.F2
