module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.UnmarkedNonemptyDetector
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono

/-!
# 非空部分の余極限の元の hammock への単射性

概要：元の全 hammock 上の検出射を構成し、非空余極限の包含との合成を回収する。
方針：元の各語の標準射の自然性と同じ余極限の普遍性を使う。
規約：同じ元の単体を保持し、添字圏の filtered 性を仮定しない。
使われ方：元の hammock の非空部分との同定。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.FirstFactor
open CategoryTheory CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C) (X Y : Paths C)

lemma detectWord_word {a b : Word} (f : a ⟶ b) :
    (graphDiagram W.paths X Y).map f ≫ detectWord W X Y b = detectWord W X Y a := by
  classical
  ext n τ
  change (Fin (n.unop.len + 1) ⥤ Zigzag W.paths a X Y) at τ
  change (if h : ∃ j, column W ((τ ⋙ WordAction.functor f).obj 0) j ≠ [] then
    some ((inclusion W X Y b).app n ⟨τ ⋙ WordAction.functor f, h⟩) else none) =
      (if h : ∃ j, column W (τ.obj 0) j ≠ [] then
        some ((inclusion W X Y a).app n ⟨τ, h⟩) else none)
  by_cases h : ∃ j, column W (τ.obj 0) j ≠ []
  · have hf : ∃ j, column W ((τ ⋙ WordAction.functor f).obj 0) j ≠ [] :=
      (nonemptyColumns_wordAction_iff W f (τ.obj 0)).2 h
    rw [dite_eq_left hf, dite_eq_left h]
    exact congrArg some (congrArg (fun k => k.app n ⟨τ, h⟩)
      (colimit.w (NonemptyGraph.wordDiagram W X Y) f))
  · have hf : ¬ ∃ j, column W ((τ ⋙ WordAction.functor f).obj 0) j ≠ [] :=
      fun he => h ((nonemptyColumns_wordAction_iff W f (τ.obj 0)).1 he)
    rw [dite_eq_right hf, dite_eq_right h]

def detector : colimitGraph W.paths X Y ⟶ OptionSpace.space (nonemptyColimit W X Y) :=
  colimitGraphDesc W.paths X Y (detectWord W X Y) (detectWord_word W X Y)

lemma graphInclusion_detector (w : Word) :
    graphInclusion W.paths X Y w ≫ detector W X Y = detectWord W X Y w :=
  graphInclusion_desc W.paths X Y _ _ w

lemma ambientMap_detector : ambientMap W X Y ≫ detector W X Y =
    OptionSpace.inclusion (nonemptyColimit W X Y) := by
  apply colimit.hom_ext
  intro w
  change inclusion W X Y w ≫ (ambientMap W X Y ≫ detector W X Y) = _
  rw [← Category.assoc, inclusion_ambientMap, Category.assoc, graphInclusion_detector,
    inclusion_detectWord]
  rfl

lemma ambientMap_injective (n : SimplexCategoryᵒᵖ) :
    Function.Injective ((ambientMap W X Y).app n) := by
  intro x y h
  apply OptionSpace.inclusion_injective (nonemptyColimit W X Y) n
  have hx := congrArg (fun k => k.app n x) (ambientMap_detector W X Y)
  have hy := congrArg (fun k => k.app n y) (ambientMap_detector W X Y)
  exact hx.symm.trans ((congrArg ((detector W X Y).app n) h).trans hy)

lemma ambientMap_mono : Mono (ambientMap W X Y) :=
  (NatTrans.mono_iff_mono_app _).2 fun n =>
    (mono_iff_injective _).2 (ambientMap_injective W X Y n)

end SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.FirstFactor
