module

public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.StructuredArrowPullbackLift
public import Mathlib.CategoryTheory.Category.Cat
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs

/-!
概要：通常の右 comma を Under と添字圏の厳密な引き戻しとして表示する。
方針：両射影を回収する関手の持ち上げと一意性を証明する。
規約：同じ宇宙の小さい圏を扱う。
使われ方：B5 の pointwise Kan の古典比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits
namespace SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison

variable {A K C : Type u} [Category.{u} A] [Category.{u} K] [Category.{u} C]
variable (c : C) (L : K ⥤ C)

/-- 概要：右 comma への関手は二つの射影で決まる。
方針：対象の構造射と元の添字の等式を合わせる。
規約：関手の等式としての一意性。
使われ方：引き戻しの普遍性の一意性。 -/
lemma structuredArrowFunctor_ext {R S : A ⥤ StructuredArrow c L}
    (h₁ : R ⋙ StructuredArrow.toUnder c L = S ⋙ StructuredArrow.toUnder c L)
    (h₂ : R ⋙ StructuredArrow.proj c L = S ⋙ StructuredArrow.proj c L) : R = S := by
  let hobj : ∀ a, R.obj a = S.obj a := by
    intro a
    refine StructuredArrow.obj_ext _ _ (CategoryTheory.Functor.congr_obj h₂ a) ?_
    have ht := Under.w (eqToHom (CategoryTheory.Functor.congr_obj h₁ a))
    rw [eqToHom_map]
    simp only [Under.eqToHom_right] at ht
    exact ht
  refine CategoryTheory.Functor.ext hobj (fun a b f ↦ ?_)
  apply StructuredArrow.hom_ext
  have hh := CategoryTheory.Functor.congr_hom h₂ f
  simp only [StructuredArrow.comp_right, StructuredArrow.eqToHom_right]
  exact hh

/-- 概要：右 comma は Under と元の添字圏の Cat 内の引き戻し。
方針：構成済みの持ち上げと両射影の回収と一意性を使う。
規約：二圏の同型で可換な四角形とは区別する。
使われ方：nerve の極限保存による局所添字の比較。 -/
lemma structuredArrow_isPullback : IsPullback (StructuredArrow.toUnder c L).toCatHom
    (StructuredArrow.proj c L).toCatHom (Under.forget c).toCatHom L.toCatHom := by
  let lift (s : PullbackCone (Under.forget c).toCatHom L.toCatHom) :
      s.pt ⟶ Cat.of (StructuredArrow c L) :=
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.structuredArrowPullbackLift c L s.fst.toFunctor s.snd.toFunctor
      (congrArg Cat.Hom.toFunctor s.condition)).toCatHom
  have hw : (StructuredArrow.toUnder c L).toCatHom ≫ (Under.forget c).toCatHom =
      (StructuredArrow.proj c L).toCatHom ≫ L.toCatHom := rfl
  apply IsPullback.of_isLimit (PullbackCone.IsLimit.mk hw lift ?_ ?_ ?_)
  · intro s
    apply Cat.Hom.ext
    exact _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.structuredArrowPullbackLift_under c L s.fst.toFunctor s.snd.toFunctor
      (congrArg Cat.Hom.toFunctor s.condition)
  · intro s
    rfl
  · intro s m hm₁ hm₂
    apply Cat.Hom.ext
    apply structuredArrowFunctor_ext c L
    · exact (congrArg Cat.Hom.toFunctor hm₁).trans (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.structuredArrowPullbackLift_under c L
        s.fst.toFunctor s.snd.toFunctor (congrArg Cat.Hom.toFunctor s.condition)).symm
    · exact congrArg Cat.Hom.toFunctor hm₂

end SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison
