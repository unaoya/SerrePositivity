module

public import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.FunctorCategory

/-!
概要：通常の関手圏の nerve の指数比較の頂点の計算。
方針：比較を内部 Hom の単体として各次数で評価する。
規約：元の通常の関手の nerve 自身と比較する。
使われ方：B5 の古典自然変換を指定された元の関手の間の射として表示する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Functor MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison

/-- 概要：指数比較は通常の関手の頂点をその nerve の関手頂点へ写す。
方針：内部 Hom の頂点を全次数の評価で照合する。
規約：通常の関手 F を指定し、像を選び直さない。
使われ方：古典随伴の単位・余単位の両端の同定。 -/
lemma nerveFunctorCategoryIso_vertex {C D : Type u} [Category.{u} C] [Category.{u} D]
    (F : C ⥤ D) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.nerveFunctorCategoryIso C D).hom.app (Opposite.op ⦋0⦌) (ComposableArrows.mk₀ F) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (nerveMap F) := by
  apply CategoryTheory.Functor.functorHom_ext
  intro n α
  apply ConcreteCategory.hom_ext
  intro σ
  have he := _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.nerveFunctorCategoryIso_uncurry C D
  let t : (nerve (C × (C ⥤ D))).obj n := σ.prod' ((nerve (C ⥤ D)).map α (ComposableArrows.mk₀ F))
  have h := ConcreteCategory.congr_hom (NatTrans.congr_app he n) t
  change (((_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.nerveFunctorCategoryIso C D).hom.app n
    ((nerve (C ⥤ D)).map α (ComposableArrows.mk₀ F))).app n (𝟙 n)) σ = _ at h
  rw [(_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.nerveFunctorCategoryIso C D).hom.naturality_apply α] at h
  change (((_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.nerveFunctorCategoryIso C D).hom.app (Opposite.op ⦋0⦌)
    (ComposableArrows.mk₀ F)).app n (α ≫ 𝟙 n)) σ = _ at h
  rw [Category.comp_id] at h
  change (((_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.nerveFunctorCategoryIso C D).hom.app (Opposite.op ⦋0⦌)
    (ComposableArrows.mk₀ F)).app n α) σ = (nerveMap F).app n σ
  refine h.trans ?_
  refine CategoryTheory.Functor.ext (fun _ ↦ rfl) (fun i j f ↦ ?_)
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  change F.map (σ.map f) ≫ (𝟙 F : F ⟶ F).app (σ.obj j) = F.map (σ.map f)
  simp only [NatTrans.id_app, Category.comp_id]

end SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison
