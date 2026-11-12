module

public import Mathlib.CategoryTheory.Comma.Over.Basic

/-!
概要：左 comma の引き戻しの持ち上げを通常の関手として構成する。
方針：Over の構造射の始点を可換性の等式で輸送する。
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
variable (L : K ⥤ C) (c : C) (P : A ⥤ Over c) (Q : A ⥤ K)
variable (h : P ⋙ Over.forget c = Q ⋙ L)

/-- 概要：可換な二つの関手を左 comma の関手へ持ち上げる。
方針：Over の構造射の始点を可換性で輸送する。
規約：通常の関手の厳密な可換性を仮定する。
使われ方：左 comma の引き戻し性。 -/
def costructuredArrowPullbackLift : A ⥤ CostructuredArrow L c :=
  Q.toCostructuredArrow L c (fun a ↦ eqToHom (Functor.congr_obj h a).symm ≫ (P.obj a).hom) (by
    intro a b f
    have hh := CategoryTheory.Functor.congr_hom h.symm f
    have hm : L.map (Q.map f) ≫ eqToHom (CategoryTheory.Functor.congr_obj h b).symm =
        eqToHom (CategoryTheory.Functor.congr_obj h a).symm ≫ (P.map f).left := by
      simpa only [Functor.comp_map, Over.forget_map, Category.assoc, eqToHom_trans,
        eqToHom_refl, Category.comp_id] using
          congrArg (fun k ↦ k ≫ eqToHom (CategoryTheory.Functor.congr_obj h b).symm) hh
    rw [← Category.assoc, hm, Category.assoc, Over.w])

/-- 概要：持ち上げの元の添字への射影は元の関手。
方針：余構造化射の定義の射影を読む。
規約：通常の関手の厳密な等式。
使われ方：第二射影の回収。 -/
lemma costructuredArrowPullbackLift_proj :
    costructuredArrowPullbackLift L c P Q h ⋙ CostructuredArrow.proj L c = Q := rfl

/-- 概要：忘却関手を等しい関手へ輸送しても元の Over の関手に戻る。
方針：関手の等式で置換し対象と射を照合する。
規約：構造射の始点の輸送を含める。
使われ方：持ち上げの第一射影。 -/
lemma overFunctorTransport_eq (R : A ⥤ C) (e : R = P ⋙ Over.forget c) :
    R.toOver c (fun a ↦ eqToHom (Functor.congr_obj e a) ≫ (P.obj a).hom) (by
      intro a b f
      have hh := CategoryTheory.Functor.congr_hom e f
      have hm : R.map f ≫ eqToHom (CategoryTheory.Functor.congr_obj e b) =
          eqToHom (CategoryTheory.Functor.congr_obj e a) ≫ (P.map f).left := by
        simpa only [Functor.comp_map, Over.forget_map, Category.assoc, eqToHom_trans,
          eqToHom_refl, Category.comp_id] using
            congrArg (fun k ↦ k ≫ eqToHom (CategoryTheory.Functor.congr_obj e b)) hh
      rw [← Category.assoc, hm, Category.assoc, Over.w]) = P := by
  subst R
  let hobj : ∀ a, Over.mk (eqToHom (Eq.refl (P.obj a).left) ≫ (P.obj a).hom) = P.obj a := by
    intro a
    rw [eqToHom_refl, Category.id_comp]
    rfl
  refine CategoryTheory.Functor.ext hobj (fun a b f ↦ ?_)
  apply Over.OverMorphism.ext
  simp only [Over.comp_left, Over.eqToHom_left]
  change (P.map f).left = eqToHom _ ≫ (P.map f).left ≫ eqToHom _
  simp only [eqToHom_refl, Category.comp_id, Category.id_comp]

/-- 概要：持ち上げの Over への射影は元の Over の関手。
方針：始点の輸送を戻す一般補題を使う。
規約：構造射そのものを回収する。
使われ方：左 comma の厳密な引き戻し性。 -/
lemma costructuredArrowPullbackLift_over :
    costructuredArrowPullbackLift L c P Q h ⋙ CostructuredArrow.toOver L c = P := by
  exact overFunctorTransport_eq c P (Q ⋙ L) h.symm

end SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison
