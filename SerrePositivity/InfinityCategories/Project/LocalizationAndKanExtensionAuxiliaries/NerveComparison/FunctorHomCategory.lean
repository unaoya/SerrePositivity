module

public import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.FunctorCategory

/-!
概要：nerve 間の関手圏のホモトピー圏と通常の関手圏との比較。
方針：関手圏の指数比較の同型を h に写し、nerve 随伴の余単位と合成する。
規約：通常の圏は同じ宇宙 u の小さい圏。
使われ方：B5 の自然変換の復元と随伴の古典比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Functor MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison

/-- 概要：二つの nerve 間の関手圏の h は通常の関手圏と同値。
方針：指数比較の逆の h と、nerve 随伴の余単位の同型を合成する。
規約：hC と hD の間の関手圏への一般の忘却に置き換えない。
使われ方：通常の自然変換と元の関手圏の h の射との同定。 -/
def nerveFunctorHomCategoryEquivalence (C D : Type u) [Category.{u} C] [Category.{u} D] :
    hoFunctor.obj ((ihom (nerve C)).obj (nerve D)) ≌ (C ⥤ D) :=
  Cat.equivOfIso (hoFunctor.mapIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.nerveFunctorCategoryIso C D).symm ≪≫
    nerveFunctorCompHoFunctorIso.app (Cat.of (C ⥤ D)))

/-- 概要：通常の関手圏の指数比較は添字への前合成に自然。
方針：指数比較の始域に関する自然性を指定された成分で評価する。
規約：通常の前合成と nerve の前合成の指定された射を比較する。
使われ方：古典随伴の whiskering と相対 Kan の制限の整合性。 -/
lemma nerveFunctorCategoryIso_precomp {A C D : Type u}
    [Category.{u} A] [Category.{u} C] [Category.{u} D] (F : A ⥤ C) :
    nerveMap ((whiskeringLeft A C D).obj F) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.nerveFunctorCategoryIso A D).hom =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.nerveFunctorCategoryIso C D).hom ≫ (pre (nerveMap F)).app (nerve D) := by
  have h := congrArg (fun s ↦ s.natTrans)
    (expComparison_whiskerLeft nerveFunctor F.toCatHom)
  have hp : (pre F.toCatHom).app (Cat.of D) =
      ((whiskeringLeft A C D).obj F).toCatHom := by
    apply uncurry_injective
    rw [MonoidalClosed.uncurry_pre]
    apply Cat.Hom.ext
    refine CategoryTheory.Functor.ext (fun x ↦ rfl) (fun x y f ↦ ?_)
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    rfl
  have ht := NatTrans.congr_app h (Cat.of D)
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.nerveFunctorCategoryIso C D).hom ≫ (pre (nerveMap F)).app (nerve D) =
    nerveFunctor.map ((pre F.toCatHom).app (Cat.of D)) ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.nerveFunctorCategoryIso A D).hom at ht
  rw [hp] at ht
  exact ht.symm

end SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison
