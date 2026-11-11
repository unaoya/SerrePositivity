module

public import Mathlib.CategoryTheory.Comma.Over.Basic

/-!
概要：通常の右 comma の引き戻しの持ち上げを構成する。
方針：構造射の終点を可換性の等式で輸送する。
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
variable (c : C) (L : K ⥤ C) (P : A ⥤ Under c) (Q : A ⥤ K)
variable (h : P ⋙ Under.forget c = Q ⋙ L)

/-- 概要：可換な二つの関手を右 comma の関手へ持ち上げる。
方針：Under の構造射を射影の可換性で輸送する。
規約：通常の関手の厳密な可換性を仮定する。
使われ方：通常の comma の引き戻し性。 -/
def structuredArrowPullbackLift : A ⥤ StructuredArrow c L :=
  Q.toStructuredArrow c L (fun a ↦ (P.obj a).hom ≫ eqToHom (Functor.congr_obj h a)) (by
    intro a b f
    have hh := CategoryTheory.Functor.congr_hom h f
    have hm : eqToHom (CategoryTheory.Functor.congr_obj h a) ≫ L.map (Q.map f) =
        (P.map f).right ≫ eqToHom (CategoryTheory.Functor.congr_obj h b) := by
      simpa only [Functor.comp_map, Under.forget_map, Category.assoc, eqToHom_trans,
        eqToHom_refl, Category.comp_id] using
          congrArg (fun k ↦ k ≫ eqToHom (CategoryTheory.Functor.congr_obj h b)) hh.symm
    rw [Category.assoc, hm, ← Category.assoc, Under.w])


/-- 概要：持ち上げの通常の添字への射影は元の関手。
方針：構造化射への持ち上げの定義を読む。
規約：関手の厳密な等式。
使われ方：引き戻しの第二射影。 -/
lemma structuredArrowPullbackLift_proj :
    structuredArrowPullbackLift c L P Q h ⋙ StructuredArrow.proj c L = Q := rfl

/-- 概要：忘却関手を等しい関手へ輸送しても元の Under の関手に戻る。
方針：関手の等式で置換し対象と射を確認する。
規約：構造射の終点の輸送を含める。
使われ方：持ち上げの第一射影の回収。 -/
lemma underFunctorTransport_eq (R : A ⥤ C) (e : P ⋙ Under.forget c = R) :
    R.toUnder c (fun a ↦ (P.obj a).hom ≫ eqToHom (Functor.congr_obj e a)) (by
      intro a b f
      have hh := CategoryTheory.Functor.congr_hom e f
      have hm : eqToHom (CategoryTheory.Functor.congr_obj e a) ≫ R.map f =
          (P.map f).right ≫ eqToHom (CategoryTheory.Functor.congr_obj e b) := by
        simpa only [Functor.comp_map, Under.forget_map, Category.assoc, eqToHom_trans,
          eqToHom_refl, Category.comp_id] using
            congrArg (fun k ↦ k ≫ eqToHom (CategoryTheory.Functor.congr_obj e b)) hh.symm
      rw [Category.assoc, hm, ← Category.assoc, Under.w]) = P := by
  subst R
  let hobj : ∀ a, Under.mk ((P.obj a).hom ≫ eqToHom (Eq.refl (P.obj a).right)) = P.obj a := by
    intro a
    rw [eqToHom_refl, Category.comp_id]
    rfl
  refine CategoryTheory.Functor.ext hobj (fun a b f ↦ ?_)
  apply Under.UnderMorphism.ext
  simp only [Under.comp_right, Under.eqToHom_right]
  change (P.map f).right = eqToHom _ ≫ (P.map f).right ≫ eqToHom _
  simp only [eqToHom_refl, Category.comp_id, Category.id_comp]

/-- 概要：持ち上げから Under への射影は元の Under の関手。
方針：終点の輸送を戻す一般補題を使う。
規約：構造射そのものを回収する。
使われ方：通常の comma の厳密な引き戻し性。 -/
lemma structuredArrowPullbackLift_under :
    structuredArrowPullbackLift c L P Q h ⋙ StructuredArrow.toUnder c L = P := by
  exact underFunctorTransport_eq c P (Q ⋙ L) h

end SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison
