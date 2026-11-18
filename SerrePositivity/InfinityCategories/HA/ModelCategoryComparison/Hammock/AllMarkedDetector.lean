module

public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.AllMarkedNative
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.OptionSpace

/-!
# 元の各語から実際の指定部分圏の hammock への検出

概要：全列が指定である元の単体を指定部分圏へ持ち上げ、その元の標準射へ送る。
方針：元の全単体作用素の指定性の保存・反映と持ち上げの回収を使う。
規約：指定部分圏の実際の hammock の点を使う。
使われ方：元の包含の単射性と空文字列部分への同定。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.AllMarked
open _root_.CategoryTheory

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C) (X Y : Paths C)

open _root_.Classical in
def detectWord (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W.paths w X Y ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.OptionSpace.space (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.AllMarked.nativeSpace W X Y) where
  app n := ↾fun τ => if h : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Holds W τ then
    some ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.AllMarked.nativeInclusion W X Y w).app n (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.AllMarked.lift W τ h)) else none
  naturality n m θ := by
    apply ConcreteCategory.hom_ext
    intro τ
    change (if h : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Holds W ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W.paths w X Y).map θ τ) then
      some ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.AllMarked.nativeInclusion W X Y w).app m (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.AllMarked.lift W ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W.paths w X Y).map θ τ) h))
      else none) = Option.map ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.AllMarked.nativeSpace W X Y).map θ)
        (if h : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Holds W τ then some ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.AllMarked.nativeInclusion W X Y w).app n (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.AllMarked.lift W τ h)) else none)
    by_cases h : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Holds W τ
    · have hθ := (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.holds_simplex_iff W τ θ).2 h
      rw [dite_eq_left hθ, dite_eq_left h, _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.AllMarked.lift_simplex W τ h θ hθ]
      exact congrArg some (congrArg (fun k => k (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.AllMarked.lift W τ h))
        ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.AllMarked.nativeInclusion W X Y w).naturality θ))
    · have hθ : ¬ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Holds W ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W.paths w X Y).map θ τ) :=
        fun he => h ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.holds_simplex_iff W τ θ).1 he)
      rw [dite_eq_right hθ, dite_eq_right h]
      rfl

lemma graphMap_detectWord (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) : _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.AllMarked.graphMap W X Y w ≫ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.AllMarked.detectWord W X Y w =
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.AllMarked.nativeInclusion W X Y w ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.OptionSpace.inclusion (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.AllMarked.nativeSpace W X Y) := by
  classical
  ext n τ
  change (if h : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Holds W ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.AllMarked.graphMap W X Y w).app n τ) then
    some ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.AllMarked.nativeInclusion W X Y w).app n (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.AllMarked.lift W ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.AllMarked.graphMap W X Y w).app n τ) h)) else none) = _
  rw [dite_eq_left (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.AllMarked.graphMap_holds W τ), _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.AllMarked.lift_reflection]
  rfl

end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.AllMarked
