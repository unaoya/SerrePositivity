module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.FunctorHomPostcompIdentity
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.ResolutionCounitComparison
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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet MonoidalClosed
lemma resolutionCounitComparison_hom_naturality
    {A B : SSet.{u}} [Quasicategory A] [Quasicategory B]
    {f : A ⟶ A} {g : B ⟶ B}
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f (𝟙 A)) (d : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso g (𝟙 B))
    {h k : A ⟶ B} (a : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom h k) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolutionCounitComparison e d h).hom ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp h k g a =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPrecomp h k f a ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolutionCounitComparison e d k).hom := by
  have he := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHom_whisker_exchange_typed e.hom a
  have hd := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHom_whisker_exchange_typed a d.inv
  have hi : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPrecomp h k (𝟙 A) a = a := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHom_precomp_id a
  rw [hi] at he
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHom_postcomp_id] at hd
  simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolutionCounitComparison, Iso.trans_hom, Iso.symm_hom,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorIso_postcomp_hom_typed]
  calc
    _ = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp f (𝟙 A) h e.hom ≫
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPrecomp (𝟙 B) g h d.inv ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp h k g a) :=
      Category.assoc _ _ _
    _ = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp f (𝟙 A) h e.hom ≫
        (a ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPrecomp (𝟙 B) g k d.inv) := congrArg (fun z => _ ≫ z) hd.symm
    _ = (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp f (𝟙 A) h e.hom ≫ a) ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPrecomp (𝟙 B) g k d.inv := (Category.assoc _ _ _).symm
    _ = (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPrecomp h k f a ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp f (𝟙 A) k e.hom) ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPrecomp (𝟙 B) g k d.inv := congrArg (fun z => z ≫ _) he
    _ = _ := Category.assoc _ _ _
end SerrePositivity.InfinityCategories.Project.DerivedCategories
