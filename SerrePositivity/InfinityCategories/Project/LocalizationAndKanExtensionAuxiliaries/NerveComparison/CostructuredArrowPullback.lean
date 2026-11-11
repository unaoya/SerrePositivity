module

public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.CostructuredArrowPullbackLift
public import Mathlib.CategoryTheory.Category.Cat
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs

/-!
概要：通常の左 comma を Over と添字圏の引き戻しとして表示する。
方針：両射影を回収する関手の持ち上げと一意性を使う。
規約：同じ宇宙の小さい圏を扱う。
使われ方：B5 の左 Kan の古典比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits
namespace SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison

variable {A K C : Type u} [Category.{u} A] [Category.{u} K] [Category.{u} C]
variable (L : K ⥤ C) (c : C)

/-- 概要：左 comma への関手は二つの射影で決まる。
方針：対象の構造射と元の添字の等式を照合する。
規約：通常の関手の等式としての一意性。
使われ方：引き戻しの一意性の証明。 -/
lemma costructuredArrowFunctor_ext {R S : A ⥤ CostructuredArrow L c}
    (h₁ : R ⋙ CostructuredArrow.toOver L c = S ⋙ CostructuredArrow.toOver L c)
    (h₂ : R ⋙ CostructuredArrow.proj L c = S ⋙ CostructuredArrow.proj L c) : R = S := by
  let hobj : ∀ a, R.obj a = S.obj a := by
    intro a
    refine CostructuredArrow.obj_ext _ _ (CategoryTheory.Functor.congr_obj h₂ a) ?_
    have ht := Over.w (eqToHom (CategoryTheory.Functor.congr_obj h₁ a))
    rw [eqToHom_map]
    simp only [Over.eqToHom_left] at ht
    exact ht
  refine CategoryTheory.Functor.ext hobj (fun a b f ↦ ?_)
  apply CostructuredArrow.hom_ext
  have hh := CategoryTheory.Functor.congr_hom h₂ f
  simp only [CostructuredArrow.comp_left, CostructuredArrow.eqToHom_left]
  exact hh

/-- 概要：左 comma は Over と元の添字圏の Cat 内の引き戻し。
方針：構成済みの持ち上げと両射影の回収と一意性を使う。
規約：通常の圏 Cat 内の厳密な引き戻し。
使われ方：nerve の極限保存による局所添字の比較。 -/
lemma costructuredArrow_isPullback : IsPullback (CostructuredArrow.toOver L c).toCatHom
    (CostructuredArrow.proj L c).toCatHom (Over.forget c).toCatHom L.toCatHom := by
  let lift (s : PullbackCone (Over.forget c).toCatHom L.toCatHom) :
      s.pt ⟶ Cat.of (CostructuredArrow L c) :=
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.costructuredArrowPullbackLift L c s.fst.toFunctor s.snd.toFunctor
      (congrArg Cat.Hom.toFunctor s.condition)).toCatHom
  have hw : (CostructuredArrow.toOver L c).toCatHom ≫ (Over.forget c).toCatHom =
      (CostructuredArrow.proj L c).toCatHom ≫ L.toCatHom := rfl
  apply IsPullback.of_isLimit (PullbackCone.IsLimit.mk hw lift ?_ ?_ ?_)
  · intro s
    apply Cat.Hom.ext
    exact _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.costructuredArrowPullbackLift_over L c s.fst.toFunctor s.snd.toFunctor
      (congrArg Cat.Hom.toFunctor s.condition)
  · intro s
    rfl
  · intro s m hm₁ hm₂
    apply Cat.Hom.ext
    apply costructuredArrowFunctor_ext L c
    · exact (congrArg Cat.Hom.toFunctor hm₁).trans (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.costructuredArrowPullbackLift_over L c
        s.fst.toFunctor s.snd.toFunctor (congrArg Cat.Hom.toFunctor s.condition)).symm
    · exact congrArg Cat.Hom.toFunctor hm₂

end SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison
