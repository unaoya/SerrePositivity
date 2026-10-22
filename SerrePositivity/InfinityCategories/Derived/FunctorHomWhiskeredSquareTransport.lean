module
public import SerrePositivity.InfinityCategories.Derived.FunctorHomWhiskerMapTransport
public import SerrePositivity.InfinityCategories.Derived.FunctorHomWhiskerHEq
/-!
概要：同じ可換四角形を実前後合成へ送り、二段前合成の射を照合する。
方針：全関手圏の関手性と端点を保つ異種等式を使う。
規約：指定射と計算上限を変更しない。使われ方：通常 tensor 比較の半自由制限。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet MonoidalClosed
lemma functorHom_precomp_postcomp_associative_heq
    {A X Y Z W : SSet.{u}} {f g : Y ⟶ Z} (d : FunctorHom f g)
    (I : A ⟶ X) (P : X ⟶ Y) (F : A ⟶ Y) (L : Z ⟶ W) (hF : F = I ≫ P) :
    HEq (functorHomPrecomp (f ≫ L) (g ≫ L) F (functorHomPostcomp f g L d))
      (functorHomPostcomp (I ≫ (P ≫ f)) (I ≫ (P ≫ g)) L
        (functorHomPrecomp (P ≫ f) (P ≫ g) I (functorHomPrecomp f g P d))) := by
  subst F
  have h := functorHomPrecomp_postcomp f g (I ≫ P) L d
  have hp := functorHomPrecomp_precomp f g P I d
  have hp' := functorHom_postcomp_heq _ _ (Category.assoc I P f)
    (Category.assoc I P g) (heq_of_eq hp).symm L
  exact (heq_of_eq h.symm).trans hp'
lemma functorHom_precomp_postcomp_square
    {A X Y Z : SSet.{u}} {f g f' g' : X ⟶ Y}
    (c : FunctorHom f g) (r : FunctorHom g g')
    (q : FunctorHom f f') (d : FunctorHom f' g')
    (h : c ≫ r = q ≫ d) (I : A ⟶ X) (L : Y ⟶ Z) :
    functorHomPostcomp (I ≫ f) (I ≫ g) L (functorHomPrecomp f g I c) ≫
        functorHomPostcomp (I ≫ g) (I ≫ g') L (functorHomPrecomp g g' I r) =
      functorHomPostcomp (I ≫ f) (I ≫ f') L (functorHomPrecomp f f' I q) ≫
        functorHomPostcomp (I ≫ f') (I ≫ g') L (functorHomPrecomp f' g' I d) := by
  have hp := congrArg (fun z => functorHomPrecomp f g' I z) h
  have hq := congrArg (fun z => functorHomPostcomp (I ≫ f) (I ≫ g') L z) hp
  simpa only [functorHomPrecomp_comp, functorHomPostcomp_comp] using! hq
end SerrePositivity.InfinityCategories
