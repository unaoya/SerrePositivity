module

public import SerrePositivity.EInfinity.Hammock.UnmarkedFirstFactorPasteRecovery
public import SerrePositivity.EInfinity.Hammock.UnmarkedNonemptyIso

/-!
# 元の非空部分の切断と貼り戻しによる包含の回収

概要：実際の切断を貼り戻すと、元の非空部分の包含自身に一致する。
方針：各語の同じ単体の回収を、元の余極限と元の非空部分の同型へ渡す。
規約：元の標準射と実際の切断射を保持する。
使われ方：反復抽出の後の貼り戻しが元の恒等射であること。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.FirstFactor
open CategoryTheory CategoryTheory.Limits

variable {C : Type u} [Category.{u} C] (W : MorphismProperty C) (X Y : Paths C)

lemma cutMap_paste (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.cutMap W w X Y ≫ FactorTarget.paste W X Y =
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedNonemptyGraph.inclusion W w X Y ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion W.paths X Y w := by
  ext n τ
  exact paste_point W τ.val τ.property

lemma colimitCut_paste : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorColimit.colimitCut W X Y ≫ FactorTarget.paste W X Y = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorColimit.ambientMap W X Y := by
  apply colimit.hom_ext
  intro w
  change _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorColimit.inclusion W X Y w ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorColimit.colimitCut W X Y ≫ FactorTarget.paste W X Y) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorColimit.inclusion W X Y w ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorColimit.ambientMap W X Y
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorColimit.inclusion_colimitCut, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorColimit.inclusion_ambientMap]
  exact cutMap_paste W X Y w

lemma nonemptyCut_paste : nonemptyCut W X Y ≫ FactorTarget.paste W X Y =
    NonemptyValue.inclusion W X Y := by
  apply (cancel_epi (nonemptyIso W X Y).hom).1
  rw [← Category.assoc, nonemptyIso_hom_cut, colimitCut_paste]
  exact (nonemptyIso_hom_inclusion W X Y).symm

end SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.FirstFactor
