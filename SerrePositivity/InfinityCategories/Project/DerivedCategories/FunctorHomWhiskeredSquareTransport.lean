module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.FunctorHomWhiskerMapTransport
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.FunctorHomWhiskerHEq
/-!
概要：同じ可換四角形を実前後合成へ送り、二段前合成の射を照合する。
方針：全関手圏の関手性と端点を保つ異種等式を使う。
規約：指定射と計算上限を変更しない。使われ方：通常 tensor 比較の半自由制限。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet MonoidalClosed
lemma functorHom_precomp_postcomp_associative_heq
    {A X Y Z W : SSet.{u}} {f g : Y ⟶ Z} (d : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom f g)
    (I : A ⟶ X) (P : X ⟶ Y) (F : A ⟶ Y) (L : Z ⟶ W) (hF : F = I ≫ P) :
    HEq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPrecomp (f ≫ L) (g ≫ L) F (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp f g L d))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp (I ≫ (P ≫ f)) (I ≫ (P ≫ g)) L
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPrecomp (P ≫ f) (P ≫ g) I (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPrecomp f g P d))) := by
  subst F
  have h := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPrecomp_postcomp f g (I ≫ P) L d
  have hp := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPrecomp_precomp f g P I d
  have hp' := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHom_postcomp_heq _ _ (Category.assoc I P f)
    (Category.assoc I P g) (heq_of_eq hp).symm L
  exact (heq_of_eq h.symm).trans hp'
lemma functorHom_precomp_postcomp_square
    {A X Y Z : SSet.{u}} {f g f' g' : X ⟶ Y}
    (c : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom f g) (r : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom g g')
    (q : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom f f') (d : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom f' g')
    (h : c ≫ r = q ≫ d) (I : A ⟶ X) (L : Y ⟶ Z) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp (I ≫ f) (I ≫ g) L (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPrecomp f g I c) ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp (I ≫ g) (I ≫ g') L (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPrecomp g g' I r) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp (I ≫ f) (I ≫ f') L (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPrecomp f f' I q) ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp (I ≫ f') (I ≫ g') L (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPrecomp f' g' I d) := by
  have hp := congrArg (fun z => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPrecomp f g' I z) h
  have hq := congrArg (fun z => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp (I ≫ f) (I ≫ g') L z) hp
  simpa only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPrecomp_comp, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp_comp] using! hq
end SerrePositivity.InfinityCategories.Project.DerivedCategories
