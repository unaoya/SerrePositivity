module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordPadding
public import Mathlib.CategoryTheory.Limits.HasLimits

/-!
# 元の padding 余極限の射の左逆

概要：元の図式から padding 図式の余極限への射は、元の標準射による左逆を持つ。
方針：語の添字を padding へ移した余錐と、元の包含への余錐の自然性を使う。
規約：逆側の合成の恒等性や弱同値性は主張しない。
使われ方：三本矢の比較ホモトピーと弱同値性の回収。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] (H : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word ⥤ C)
  [HasColimit H] [HasColimit (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.paddingFunctor ⋙ H)]

def paddingColimitMap : colimit H ⟶ colimit (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.paddingFunctor ⋙ H) :=
  colimMap (Functor.whiskerRight _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.paddingInclusionNat H)

def paddingColimitRetraction : colimit (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.paddingFunctor ⋙ H) ⟶ colimit H :=
  colimit.pre H _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.paddingFunctor

lemma paddingColimitRetraction_fac (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) :
    colimit.ι (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.paddingFunctor ⋙ H) a ≫ paddingColimitRetraction H =
      colimit.ι H (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.paddingFunctor.obj a) := colimit.ι_pre H _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.paddingFunctor a

lemma paddingColimitMap_retraction : paddingColimitMap H ≫ paddingColimitRetraction H =
    𝟙 (colimit H) := by
  apply colimit.hom_ext
  intro a
  change colimit.ι H a ≫
    (colimMap (Functor.whiskerRight _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.paddingInclusionNat H) ≫
      paddingColimitRetraction H) = colimit.ι H a ≫ 𝟙 _
  rw [← Category.assoc, ι_colimMap, Category.assoc, paddingColimitRetraction_fac,
    Category.comp_id]
  exact colimit.w H (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.paddingInclusionNat.app a)

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
