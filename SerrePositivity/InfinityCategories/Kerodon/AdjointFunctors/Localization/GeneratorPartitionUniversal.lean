module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.GeneratorPartition

/-!
# 元の自由圏の二つの生成部分の普遍性

概要：指定生成矢と非指定生成矢からの関手は一意に元の Paths C へ拡張する。
方針：両部分の制限の等式を元の各生成矢に戻し、自由圏の関手の外延性を使う。
規約：対象表示の移送を含む元の関手の等式で普遍性を述べる。
使われ方：Dwyer–Kan 比較補題2.3で使う、同じ対象上の自由積分解。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v u' v'
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C)
  {D : Type u'} [Category.{v'} D]

lemma jointly_ext {F G : Paths C ⥤ D}
    (hm : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MarkedGeneratorPaths.inclusion W ⋙ F = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MarkedGeneratorPaths.inclusion W ⋙ G)
    (hu : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MarkedGeneratorPaths.inclusion (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.unmarked W) ⋙ F =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MarkedGeneratorPaths.inclusion (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.unmarked W) ⋙ G) : F = G := by
  classical
  have ho : F.obj = G.obj := funext (fun X => Functor.congr_obj hm X)
  apply Paths.ext_functor (F := F) (G := G) ho
  intro X Y f
  apply eq_of_heq
  simp only [heq_eqToHom_comp_iff, heq_comp_eqToHom_iff]
  by_cases hf : W f
  · exact CategoryTheory.Functor.hcongr_hom hm
      (Quiver.Hom.toPath (show @Quiver.Hom (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MarkedGeneratorPaths.quiver W) _ X Y from ⟨f, hf⟩))
  · exact CategoryTheory.Functor.hcongr_hom hu
      (Quiver.Hom.toPath (show @Quiver.Hom (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MarkedGeneratorPaths.quiver (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.unmarked W)) _ X Y from
        ⟨f, hf⟩))

lemma extend_unique (F : Paths (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MarkedGeneratorPaths.quiver W) ⥤ D)
    (G : Paths (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MarkedGeneratorPaths.quiver (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.unmarked W)) ⥤ D)
    (h : ∀ X : C, F.obj X = G.obj X) (H : Paths C ⥤ D)
    (hm : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MarkedGeneratorPaths.inclusion W ⋙ H = F)
    (hu : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MarkedGeneratorPaths.inclusion (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.unmarked W) ⋙ H = G) :
    H = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.extendFunctor W F G h :=
  jointly_ext W (hm.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.marked_fac W F G h).symm)
    (hu.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.unmarked_fac W F G h).symm)

lemma existsUnique_extension (F : Paths (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MarkedGeneratorPaths.quiver W) ⥤ D)
    (G : Paths (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MarkedGeneratorPaths.quiver (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.unmarked W)) ⥤ D)
    (h : ∀ X : C, F.obj X = G.obj X) :
    ∃! H : Paths C ⥤ D, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MarkedGeneratorPaths.inclusion W ⋙ H = F ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MarkedGeneratorPaths.inclusion (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.unmarked W) ⋙ H = G := by
  refine ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.extendFunctor W F G h, ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.marked_fac W F G h, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.unmarked_fac W F G h⟩, ?_⟩
  intro H hH
  exact extend_unique W F G h H hH.1 hH.2

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
