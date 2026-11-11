module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedRefinementRecovery
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ColimitGraph

/-!
# 元の refined hammock 単体と同じ標準射の回収

概要：元の全図式の回収を、元の hammock graph の単体と余極限の標準射へ移す。
方針：同じ WordAction の nerve と標準余錐の自然性を使う。
規約：元の単体 τ 自身への厳密な回収である。
使われ方：指定 prefix と残りの分解と元の hammock の比較。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory

abbrev refinedWord (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) (i : Fin w.length) : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordColumnSplit.before w i) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .forward))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .forward))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .forward) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordColumnSplit.after w i))

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C)
  {w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} {X Y : Paths C} {n : SimplexCategoryᵒᵖ}
  (τ : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W.paths w X Y).obj n) (i : Fin w.length)
  (h : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedGeneratorColumns.column W (τ.obj 0) i ≠ [])

def refinedSimplex : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W.paths (refinedWord w i) X Y).obj n := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachmentDiagrams.refinedFunctor W τ i h

lemma refinedSimplex_recovery :
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram.graphDiagram W.paths X Y).map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.refinementMap W τ i h)).app n
      (refinedSimplex W τ i h) = τ := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.refinedFunctor_recovery W τ i h

lemma refinedSimplex_inclusion :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion W.paths X Y (refinedWord w i)).app n (refinedSimplex W τ i h) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion W.paths X Y w).app n τ := by
  have hn := congrArg (fun f => f.app n (refinedSimplex W τ i h))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion_naturality W.paths X Y (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.refinementMap W τ i h))
  have hr := congrArg
    (fun z : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W.paths w X Y).obj n => (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion W.paths X Y w).app n z)
    (refinedSimplex_recovery W τ i h)
  exact hn.symm.trans hr

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
