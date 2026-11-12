module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.FunctorHomPostcompIdentityMap
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.FunctorHomPrecompIdentityMorphism
/-!
概要：恒等二射の水平作用に対する比較四角形を正規化する。
方針：実前後合成の恒等射保存を圏一般で適用する。
規約：比較の値を変更しない。使われ方：一般 cell 合成の模型変更。
-/
@[expose] public section
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet
lemma functorIso_hom_square_of_identity_horizontal {X Y Z : SSet.{u}}
    (F : X ⟶ Y) (G : Y ⟶ Z) {K0 K1 : X ⟶ Z}
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (F ≫ G) K0) (b : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (F ≫ G) K1)
    (r : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom K0 K1) (f : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom F F) (g : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom G G)
    (hf : f = 𝟙 _) (hg : g = 𝟙 _)
    (h : a.hom ≫ r =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp F F G f ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPrecomp G G F g) ≫ b.hom) :
    a.hom ≫ r = b.hom := by
  simpa only [hf, hg, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp_identity, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPrecomp_identity,
    Category.id_comp] using h
end SerrePositivity.InfinityCategories.Project.DerivedCategories
