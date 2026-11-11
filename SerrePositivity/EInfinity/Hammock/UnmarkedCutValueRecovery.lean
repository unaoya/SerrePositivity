module

public import SerrePositivity.EInfinity.Hammock.UnmarkedNonemptyIso
public import SerrePositivity.EInfinity.Hammock.UnmarkedFirstFactorValue
public import SerrePositivity.EInfinity.Hammock.UnmarkedFactorTargetValue

/-!
# 元の非空部分上の切断による非指定文字列の回収

概要：実際の切断射の生成矢と残りの評価から、元の文字列評価を回収する。
方針：元の各語での三因子の値を余極限と既存の非空部分の同型へ渡す。
規約：元の標準射・実際の切断射・元の文字列評価を保持する。
使われ方：残りの文字列の tail と長さの厳密な減少。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.FirstFactor
open CategoryTheory CategoryTheory.Limits

variable {C : Type u} [Category.{u} C] (W : MorphismProperty C) {X Y : Paths C}

lemma point_wordValue {w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} {n : SimplexCategoryᵒᵖ}
    (τ : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W.paths w X Y).obj n) (h : ∃ j, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedGeneratorColumns.column W (τ.obj 0) j ≠ []) :
    (FactorTarget.wordValue W X Y).app n (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorPoint.point W τ h) = value W (τ.obj 0) := by
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorPoint.generator W τ h).val ::
    (colimitValue W (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorPoint.generator W τ h).val.right Y).app n (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorPoint.rightPoint W τ h) = _
  have hr := colimitValue_inclusion W (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorPoint.generator W τ h).val.right Y
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.residualWord w (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedAttachedPrefix.index W τ h))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachmentDiagrams.residualFunctor W τ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedAttachedPrefix.index W τ h) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedAttachedPrefix.nonempty W τ h))
  exact (congrArg (List.cons (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorPoint.generator W τ h).val) hr).trans
    (AttachedPrefix.value_cons_residual W τ h 0).symm

lemma colimitCut_wordValue (X Y : Paths C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorColimit.colimitCut W X Y ≫ FactorTarget.wordValue W X Y = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorColimit.ambientMap W X Y ≫ colimitValue W X Y := by
  apply colimit.hom_ext
  intro w
  change _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorColimit.inclusion W X Y w ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorColimit.colimitCut W X Y ≫ FactorTarget.wordValue W X Y) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorColimit.inclusion W X Y w ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorColimit.ambientMap W X Y ≫ colimitValue W X Y)
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorColimit.inclusion_colimitCut, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorColimit.inclusion_ambientMap]
  ext n τ
  exact (point_wordValue W τ.val τ.property).trans (colimitValue_inclusion W X Y w τ.val).symm

lemma nonemptyCut_wordValue (X Y : Paths C) :
    nonemptyCut W X Y ≫ FactorTarget.wordValue W X Y =
      NonemptyValue.inclusion W X Y ≫ colimitValue W X Y := by
  apply (cancel_epi (nonemptyIso W X Y).hom).1
  rw [← Category.assoc, nonemptyIso_hom_cut, ← Category.assoc, nonemptyIso_hom_inclusion]
  exact colimitCut_wordValue W X Y

end SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.FirstFactor
