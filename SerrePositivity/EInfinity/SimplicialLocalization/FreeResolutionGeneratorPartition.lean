module

public import SerrePositivity.EInfinity.SimplicialLocalization.FreeResolution
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MarkedGeneratorCategory
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.GeneratorPartitionUniversal

/-!
# 元の自由解像の全次数の指定生成矢と自由積の普遍性

概要：指定生成矢の自由圏と二つの生成部分の普遍性を、元の自由解像の各次数へ代入する。
方針：最外層の自由相対圏の元の生成圏と W.paths をそのまま使う。
規約：零次と全単体次数を含み、恒等文字も保持する。高次比較の弱同値性は後続。
使われ方：Dwyer–Kan 比較補題2.3の各自由次数への適用。
-/

@[expose] public section
universe u u' v'
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.SimplicialLocalization
open CategoryTheory
open SerrePositivity.HomotopyFunctionComplex

def freeResolutionGeneratorBase (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) (n : SimplexCategoryᵒᵖ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u} := ComonadResolutionOperators.power _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.freeRelativeComonad C n.unop.len

lemma freeResolution_eq_freeGeneratorBase (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) (n : SimplexCategoryᵒᵖ) :
    (freeResolution C).obj n = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.freeRelativeFunctor.obj (freeResolutionGeneratorBase C n) := rfl

def freeResolutionMarkedEquivalence (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) (n : SimplexCategoryᵒᵖ) :
    Paths (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MarkedGeneratorPaths.quiver (freeResolutionGeneratorBase C n).weakEquivalences) ≌
      WideSubcategory ((freeResolution C).obj n).weakEquivalences :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MarkedGeneratorCategory.equivalence (freeResolutionGeneratorBase C n).weakEquivalences

lemma freeResolutionMarkedEquivalence_inclusion (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u})
    (n : SimplexCategoryᵒᵖ) :
    (freeResolutionMarkedEquivalence C n).functor ⋙
      wideSubcategoryInclusion ((freeResolution C).obj n).weakEquivalences =
        _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MarkedGeneratorPaths.inclusion (freeResolutionGeneratorBase C n).weakEquivalences := rfl

lemma freeResolution_existsUnique_extension (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u})
    (n : SimplexCategoryᵒᵖ) {D : Type u'} [Category.{v'} D]
    (F : Paths (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MarkedGeneratorPaths.quiver (freeResolutionGeneratorBase C n).weakEquivalences) ⥤ D)
    (G : Paths (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MarkedGeneratorPaths.quiver
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.unmarked (freeResolutionGeneratorBase C n).weakEquivalences)) ⥤ D)
    (h : ∀ X : (freeResolutionGeneratorBase C n).category, F.obj X = G.obj X) :
    ∃! H : ((freeResolution C).obj n).category ⥤ D,
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MarkedGeneratorPaths.inclusion (freeResolutionGeneratorBase C n).weakEquivalences ⋙ H = F ∧
        _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MarkedGeneratorPaths.inclusion
          (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.unmarked (freeResolutionGeneratorBase C n).weakEquivalences) ⋙ H =
            G :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.existsUnique_extension (freeResolutionGeneratorBase C n).weakEquivalences F G h

end SerrePositivity.EInfinity.SimplicialLocalization
