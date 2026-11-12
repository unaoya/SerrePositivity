module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorColimit
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedNonemptyReflection
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.OptionSpace

/-!
# 元の各語の非空部分の余極限への検出写像

概要：非空の列を持つ単体は元の非空余極限へ送り、それ以外を none に送る。
方針：非空条件の全単体作用素による保存・反映と元の標準射の自然性を使う。
規約：非空の場合は元の同じ単体の標準射を使う。
使われ方：元の全 hammock からの検出射と包含の単射性。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C) (X Y : Paths C)

open Classical in
def detectWord (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W.paths w X Y ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.OptionSpace.space (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorColimit.nonemptyColimit W X Y) where
  app n := ↾fun τ => if h : ∃ j, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedGeneratorColumns.column W (τ.obj 0) j ≠ [] then
    some ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorColimit.inclusion W X Y w).app n ⟨τ, h⟩) else none
  naturality n m θ := by
    apply ConcreteCategory.hom_ext
    intro τ
    change (if h : ∃ j, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedGeneratorColumns.column W (((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W.paths w X Y).map θ τ).obj 0) j ≠ [] then
      some ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorColimit.inclusion W X Y w).app m ⟨(_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W.paths w X Y).map θ τ, h⟩) else none) =
      Option.map ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorColimit.nonemptyColimit W X Y).map θ)
        (if h : ∃ j, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedGeneratorColumns.column W (τ.obj 0) j ≠ [] then
          some ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorColimit.inclusion W X Y w).app n ⟨τ, h⟩) else none)
    by_cases h : ∃ j, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedGeneratorColumns.column W (τ.obj 0) j ≠ []
    · have hθ := (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.nonemptyColumns_simplex_iff W τ θ).2 h
      rw [dite_eq_left hθ, dite_eq_left h]
      exact congrArg some (congrArg (fun k => k ⟨τ, h⟩) ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorColimit.inclusion W X Y w).naturality θ))
    · have hθ : ¬ ∃ j, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedGeneratorColumns.column W (((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W.paths w X Y).map θ τ).obj 0) j ≠ [] :=
        fun he => h ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.nonemptyColumns_simplex_iff W τ θ).1 he)
      rw [dite_eq_right hθ, dite_eq_right h]
      rfl

lemma inclusion_detectWord (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedNonemptyGraph.inclusion W w X Y ≫ detectWord W X Y w =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorColimit.inclusion W X Y w ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.OptionSpace.inclusion (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorColimit.nonemptyColimit W X Y) := by
  classical
  ext n τ
  exact dite_eq_left τ.property

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
