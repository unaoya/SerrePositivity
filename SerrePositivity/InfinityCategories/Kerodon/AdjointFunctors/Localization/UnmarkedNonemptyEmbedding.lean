module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedNonemptyDetector
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono

/-!
# 非空部分の余極限の元の hammock への単射性

概要：元の全 hammock 上の検出射を構成し、非空余極限の包含との合成を回収する。
方針：元の各語の標準射の自然性と同じ余極限の普遍性を使う。
規約：同じ元の単体を保持し、添字圏の filtered 性を仮定しない。
使われ方：元の hammock の非空部分との同定。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedNonemptyEmbedding
open CategoryTheory CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C) (X Y : Paths C)

lemma detectWord_word {a b : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} (f : a ⟶ b) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram.graphDiagram W.paths X Y).map f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.detectWord W X Y b = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.detectWord W X Y a := by
  classical
  ext n τ
  change (Fin (n.unop.len + 1) ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W.paths a X Y) at τ
  change (if h : ∃ j, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedGeneratorColumns.column W ((τ ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.functor f).obj 0) j ≠ [] then
    some ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorColimit.inclusion W X Y b).app n ⟨τ ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.functor f, h⟩) else none) =
      (if h : ∃ j, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedGeneratorColumns.column W (τ.obj 0) j ≠ [] then
        some ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorColimit.inclusion W X Y a).app n ⟨τ, h⟩) else none)
  by_cases h : ∃ j, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedGeneratorColumns.column W (τ.obj 0) j ≠ []
  · have hf : ∃ j, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedGeneratorColumns.column W ((τ ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.functor f).obj 0) j ≠ [] :=
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.nonemptyColumns_wordAction_iff W f (τ.obj 0)).2 h
    rw [dite_eq_left hf, dite_eq_left h]
    exact congrArg some (congrArg (fun k => k.app n ⟨τ, h⟩)
      (colimit.w (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedNonemptyWordDiagram.wordDiagram W X Y) f))
  · have hf : ¬ ∃ j, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedGeneratorColumns.column W ((τ ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.functor f).obj 0) j ≠ [] :=
      fun he => h ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.nonemptyColumns_wordAction_iff W f (τ.obj 0)).1 he)
    rw [dite_eq_right hf, dite_eq_right h]

def detector : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph W.paths X Y ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.OptionSpace.space (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorColimit.nonemptyColimit W X Y) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraphDesc W.paths X Y (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.detectWord W X Y) (detectWord_word W X Y)

lemma graphInclusion_detector (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion W.paths X Y w ≫ detector W X Y = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.detectWord W X Y w :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion_desc W.paths X Y _ _ w

lemma ambientMap_detector : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorColimit.ambientMap W X Y ≫ detector W X Y =
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.OptionSpace.inclusion (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorColimit.nonemptyColimit W X Y) := by
  apply colimit.hom_ext
  intro w
  change _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorColimit.inclusion W X Y w ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorColimit.ambientMap W X Y ≫ detector W X Y) = _
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorColimit.inclusion_ambientMap, Category.assoc, graphInclusion_detector,
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.inclusion_detectWord]
  rfl

lemma ambientMap_injective (n : SimplexCategoryᵒᵖ) :
    Function.Injective ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorColimit.ambientMap W X Y).app n) := by
  intro x y h
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.OptionSpace.inclusion_injective (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorColimit.nonemptyColimit W X Y) n
  have hx := congrArg (fun k => k.app n x) (ambientMap_detector W X Y)
  have hy := congrArg (fun k => k.app n y) (ambientMap_detector W X Y)
  exact hx.symm.trans ((congrArg ((detector W X Y).app n) h).trans hy)

lemma ambientMap_mono : Mono (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorColimit.ambientMap W X Y) :=
  (NatTrans.mono_iff_mono_app _).2 fun n =>
    (mono_iff_injective _).2 (ambientMap_injective W X Y n)

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedNonemptyEmbedding
