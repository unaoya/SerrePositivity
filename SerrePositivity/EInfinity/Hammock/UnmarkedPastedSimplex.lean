module

public import SerrePositivity.EInfinity.Hammock.UnmarkedPastedColumn
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedSingletonGenerator
public import SerrePositivity.EInfinity.Hammock.UnmarkedFactorPasteValue
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorPoint

/-!
# 任意の三因子の元の単体による貼り戻しと同じ生成矢

概要：指定 prefix と残りの元の単体を貼り、最初の非指定列と同じ生成矢を回収する。
方針：元の連結関手と全行の指定性・元の一文字の列を使う。
規約：元の任意の語・全行・全縦射を保持する。
使われ方：貼り戻し後の抽出による任意の三因子の回収。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.Pasted
open CategoryTheory

variable {C : Type u} [Category.{u} C] (W : MorphismProperty C)
  {a b : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} {X Y : Paths C} {n : SimplexCategoryᵒᵖ} (g : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorTarget.Index W)
  (σ : (AllMarked.nativeGraph W X g.val.left a).obj n)
  (τ : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W.paths b g.val.right Y).obj n)

def simplex : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W.paths (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append a (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .forward)) b) X Y).obj n :=
  (((AllMarked.graphMap W X g.val.left a).app n σ).prod'
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowSimplex W.paths g.val.hom.toPath n) ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendFunctor.functor).prod' τ ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendFunctor.functor

lemma simplex_nonempty : ∃ j, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedGeneratorColumns.column W ((simplex W g σ τ).obj 0) j ≠ [] :=
  ⟨columnIndex a b, fun he => List.cons_ne_nil _ _
    ((column_generator W g (((AllMarked.graphMap W X g.val.left a).app n σ).obj 0)
      (τ.obj 0)).symm.trans he)⟩

lemma simplex_firstColumn (h : ∃ j, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedGeneratorColumns.column W ((simplex W g σ τ).obj 0) j ≠ []) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedAttachedPrefix.index W (simplex W g σ τ) h = columnIndex a b :=
  firstColumn_eq W g (((AllMarked.graphMap W X g.val.left a).app n σ).obj 0) (τ.obj 0)
    (AllMarked.graphMap_holds W σ 0) h

lemma simplex_generator (h : ∃ j, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedGeneratorColumns.column W ((simplex W g σ τ).obj 0) j ≠ []) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorPoint.generator W (simplex W g σ τ) h).val = g.val := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rowGenerator_of_singleton W (simplex W g σ τ) _ _ g.val
  exact (congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedGeneratorColumns.column W ((simplex W g σ τ).obj 0)) (simplex_firstColumn W g σ τ h)).trans
    (column_generator W g (((AllMarked.graphMap W X g.val.left a).app n σ).obj 0) (τ.obj 0))

end SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.Pasted
