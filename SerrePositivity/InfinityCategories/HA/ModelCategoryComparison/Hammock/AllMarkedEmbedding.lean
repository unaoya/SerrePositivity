module

public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.AllMarkedDetector
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono

/-!
# 実際の指定部分圏の hammock の元の包含の単射性

概要：元の全 hammock 上の検出射を構成し、指定部分圏からの包含との合成を回収する。
方針：元の全語の自然性と同じ余極限の普遍性を使う。
規約：実際の包含射自身の全次数の単射性を証明する。
使われ方：空文字列部分との同型。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.AllMarked
open _root_.CategoryTheory _root_.CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C) (X Y : Paths C)

lemma detectWord_word {a b : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} (f : a ⟶ b) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram.graphDiagram W.paths X Y).map f ≫ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.AllMarked.detectWord W X Y b = _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.AllMarked.detectWord W X Y a := by
  classical
  ext n τ
  change (Fin (n.unop.len + 1) ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W.paths a X Y) at τ
  change (if h : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Holds W (τ ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.functor f) then
    some ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.AllMarked.nativeInclusion W X Y b).app n (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.AllMarked.lift W (τ ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.functor f) h)) else none) =
      (if h : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Holds W τ then some ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.AllMarked.nativeInclusion W X Y a).app n (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.AllMarked.lift W τ h)) else none)
  by_cases h : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Holds W τ
  · have hf := (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.holds_word_iff W f τ).2 h
    rw [dite_eq_left hf, dite_eq_left h]
    have he := congrArg ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.AllMarked.nativeInclusion W X Y b).app n) (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.AllMarked.lift_word W f τ h hf)
    have hn := congrArg (fun k => k.app n (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.AllMarked.lift W τ h))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion_naturality (⊤ : MorphismProperty (WideSubcategory W.paths)) ⟨X⟩ ⟨Y⟩ f)
    exact congrArg some (he.trans hn)
  · have hf : ¬ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Holds W (τ ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.functor f) := fun he => h ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.holds_word_iff W f τ).1 he)
    rw [dite_eq_right hf, dite_eq_right h]

def detector : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph W.paths X Y ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.OptionSpace.space (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.AllMarked.nativeSpace W X Y) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraphDesc W.paths X Y (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.AllMarked.detectWord W X Y) (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.AllMarked.detectWord_word W X Y)

lemma graphInclusion_detector (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion W.paths X Y w ≫ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.AllMarked.detector W X Y = _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.AllMarked.detectWord W X Y w :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion_desc W.paths X Y _ _ w

lemma inclusion_detector : _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.AllMarked.inclusion W X Y ≫ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.AllMarked.detector W X Y =
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.OptionSpace.inclusion (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.AllMarked.nativeSpace W X Y) := by
  apply colimit.hom_ext
  intro w
  change _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.AllMarked.nativeInclusion W X Y w ≫ (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.AllMarked.inclusion W X Y ≫ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.AllMarked.detector W X Y) =
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.AllMarked.nativeInclusion W X Y w ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.OptionSpace.inclusion (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.AllMarked.nativeSpace W X Y)
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.AllMarked.nativeInclusion_inclusion, Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.AllMarked.graphInclusion_detector,
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.AllMarked.graphMap_detectWord]

lemma inclusion_injective (n : SimplexCategoryᵒᵖ) :
    Function.Injective ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.AllMarked.inclusion W X Y).app n) := by
  intro x y h
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.OptionSpace.inclusion_injective (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.AllMarked.nativeSpace W X Y) n
  have hx := congrArg (fun k => k.app n x) (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.AllMarked.inclusion_detector W X Y)
  have hy := congrArg (fun k => k.app n y) (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.AllMarked.inclusion_detector W X Y)
  exact hx.symm.trans ((congrArg ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.AllMarked.detector W X Y).app n) h).trans hy)

lemma inclusion_mono : Mono (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.AllMarked.inclusion W X Y) :=
  (NatTrans.mono_iff_mono_app _).2 fun n => (mono_iff_injective _).2 (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.AllMarked.inclusion_injective W X Y n)

end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.AllMarked
