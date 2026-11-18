module

public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedValueAppend
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedRefinementRecovery
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedAttachedPrefix

/-!
# 元の最初の切断の三因子の文字列評価

概要：指定 prefix は空、中央の生成矢は同じ一文字、全体は元の値に戻る。
方針：元の全列の指定性、貼り戻しの連結則と元の refinedFunctor の回収を使う。
規約：全行で元の同じ生成矢・prefix・残りを保持する。
使われ方：残りの文字列が元の先頭を除いたものになる式と長さの反復。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.AttachedPrefix
open _root_.CategoryTheory

variable {C : Type u} [Category.{u} C] (W : MorphismProperty C)
  {w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} {X Y : Paths C} {n : SimplexCategoryᵒᵖ}
  (τ : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W.paths w X Y).obj n) (h : ∃ j, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedGeneratorColumns.column W (τ.obj 0) j ≠ [])

lemma prefix_value (d : Fin (n.unop.len + 1)) : _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.value W ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedAttachedPrefix.functor W τ h).obj d) = [] :=
  _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.value_eq_nil_of_marked W _ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedAttachedPrefix.arrow_mem W τ h d)

lemma generator_value (d : Fin (n.unop.len + 1)) :
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.value W ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachmentDiagrams.generatorBlock W τ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedAttachedPrefix.index W τ h) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedAttachedPrefix.nonempty W τ h)).obj d) =
      [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rowGenerator W τ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedAttachedPrefix.index W τ h) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedAttachedPrefix.nonempty W τ h)] := by
  classical
  rw [show ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachmentDiagrams.generatorBlock W τ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedAttachedPrefix.index W τ h) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedAttachedPrefix.nonempty W τ h)).obj d) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardZigzag.obj ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rowGeneratorMap W τ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedAttachedPrefix.index W τ h) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedAttachedPrefix.nonempty W τ h)).app d) from rfl,
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.value_forward]
  change (if W (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rowGenerator W τ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedAttachedPrefix.index W τ h) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedAttachedPrefix.nonempty W τ h)).hom then [] else
    [] ++ [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rowGenerator W τ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedAttachedPrefix.index W τ h) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedAttachedPrefix.nonempty W τ h)]) = _
  rw [ite_eq_right (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.fixedRowCut W τ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedAttachedPrefix.index W τ h) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedAttachedPrefix.nonempty W τ h) d).unmarked]
  rfl

lemma refined_value (d : Fin (n.unop.len + 1)) :
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.value W ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachmentDiagrams.refinedFunctor W τ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedAttachedPrefix.index W τ h) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedAttachedPrefix.nonempty W τ h)).obj d) =
      _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.value W (τ.obj d) := by
  have hr := congrArg (fun F => F.obj d)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.refinedFunctor_recovery W τ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedAttachedPrefix.index W τ h) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedAttachedPrefix.nonempty W τ h))
  exact (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.value_wordAction W
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.refinementMap W τ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedAttachedPrefix.index W τ h) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedAttachedPrefix.nonempty W τ h))
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachmentDiagrams.refinedFunctor W τ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedAttachedPrefix.index W τ h) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedAttachedPrefix.nonempty W τ h)).obj d)).symm.trans
      (congrArg (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.value W) hr)

lemma value_cons_residual (d : Fin (n.unop.len + 1)) : _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.value W (τ.obj d) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rowGenerator W τ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedAttachedPrefix.index W τ h) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedAttachedPrefix.nonempty W τ h) ::
      _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.value W ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachmentDiagrams.residualFunctor W τ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedAttachedPrefix.index W τ h) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedAttachedPrefix.nonempty W τ h)).obj d) := by
  rw [← _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.AttachedPrefix.refined_value W τ h d]
  change _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.value W (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.obj
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedAttachedPrefix.functor W τ h).obj d)
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachmentDiagrams.generatorBlock W τ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedAttachedPrefix.index W τ h) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedAttachedPrefix.nonempty W τ h)).obj d))
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachmentDiagrams.residualFunctor W τ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedAttachedPrefix.index W τ h) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedAttachedPrefix.nonempty W τ h)).obj d)) = _
  rw [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.value_append, _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.value_append, _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.AttachedPrefix.prefix_value, _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.AttachedPrefix.generator_value]
  rfl

end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.AttachedPrefix
