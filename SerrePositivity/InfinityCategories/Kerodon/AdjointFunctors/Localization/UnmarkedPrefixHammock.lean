module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedAttachedPrefix
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MarkedZigzagLift

/-!
# 固定生成矢の始域までの実際の W-hammock

概要：最初の非指定生成矢までの prefix の全行を、元の指定部分圏の hammock に回収する。
方針：証明済みの全列・全縦射の所属と元の包含への回収式を使う。
規約：元の指定部分圏を使い、弱比較や自然性を入力にしない。
使われ方：元の hammock の自由積分解の最初の因子。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C)
  {w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} {X Y : Paths C} {n : SimplexCategoryᵒᵖ}
  (τ : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W.paths w X Y).obj n) (h0 : ∃ j, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedGeneratorColumns.column W (τ.obj 0) j ≠ [])

def markedFunctor := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MarkedZigzagLift.liftFunctor W.paths (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedAttachedPrefix.functor W τ h0) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedAttachedPrefix.arrow_mem W τ h0)

lemma markedFunctor_inclusion :
    markedFunctor W τ h0 ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeZigzagFunctor.functor (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MarkedZigzagLift.inclusion W.paths) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedAttachedPrefix.functor W τ h0 := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MarkedZigzagLift.liftFunctor_inclusion W.paths _ _

def markedSimplex :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph (⊤ : MorphismProperty (WideSubcategory W.paths))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordColumnSplit.before w (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedAttachedPrefix.index W τ h0)) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .forward))
      (⟨X⟩ : WideSubcategory W.paths)
      (⟨(_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rowGenerator W τ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedAttachedPrefix.index W τ h0) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedAttachedPrefix.nonempty W τ h0)).left⟩ :
        WideSubcategory W.paths)).obj n := markedFunctor W τ h0

lemma markedSimplex_inclusion :
    (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeZigzagFunctor.functor (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MarkedZigzagLift.inclusion W.paths))).app n
      (markedSimplex W τ h0) = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedAttachedPrefix.functor W τ h0 := markedFunctor_inclusion W τ h0

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
