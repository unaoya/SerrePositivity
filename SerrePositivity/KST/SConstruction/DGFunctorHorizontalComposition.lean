module
public import SerrePositivity.KST.SConstruction.DGFunctorWhiskering

/-! # dg 関手 Hom end の元の横合成と交換式
概要：前後合成と縦合成で、全次数 Hom の横合成を元の対象ごとに構成する。
方針：もう一方の横合成との一致を、元の全 Hom 自然性と signed braiding で証明する。
規約：パラメータの交換を省略しない。使われ方：dg 入力の高次合成の整合性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w t
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits MonoidalCategory
open SerrePositivity.DifferentialGraded

/-- 元の全 Hom 自然性は、任意の斉次パラメータを保つ横方向の交換式を与える。 -/
lemma dgFunctorHorizontalNaturality (A : Type u) [CommRing A]
    (E : Type w) [DGCategory A E] [Small.{u} E] (B : Type t) [DGCategory A B]
    (G₀ G₁ : DGFunctor A E B) (x y : E) {K : Complex A}
    (a : K ⟶ homObject A E x y) :
    ((a ≫ G₀.map x y) ⊗ₘ dgFunctorHomπ A E B G₀ G₁ y) ≫ eComp (Complex A) _ _ _ =
      (β_ K (dgFunctorHom A E B G₀ G₁)).hom ≫
        (dgFunctorHomπ A E B G₀ G₁ x ⊗ₘ (a ≫ G₁.map x y)) ≫ eComp (Complex A) _ _ _ := by
  have h := congrArg (fun k =>
    ((a ⊗ₘ 𝟙 (dgFunctorHom A E B G₀ G₁)) ≫
      (β_ (dgFunctorHom A E B G₀ G₁) (homObject A E x y)).inv) ≫ k)
    (dgFunctorHomπ_naturality A E B G₀ G₁ x y)
  simp only [Category.assoc, Iso.inv_hom_id_assoc] at h
  rw [BraidedCategory.braiding_inv_naturality_assoc] at h
  simp only [tensorHom_comp_tensorHom_assoc, Category.id_comp] at h
  rw [← SymmetricCategory.braiding_swap_eq_inv_braiding] at h
  exact h

variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (B : Type t) [DGCategory A B]
  (F₀ F₁ : DGFunctor A D E) (G₀ G₁ : DGFunctor A E B)

/-- 二つの元の全次数 Hom パラメータによる横合成の chain map。 -/
def dgFunctorHorizontal :
    dgFunctorHom A D E F₀ F₁ ⊗ dgFunctorHom A E B G₀ G₁ ⟶
      dgFunctorHom A D B (F₀.comp G₀) (F₁.comp G₁) :=
  (dgFunctorHomPost A D E B G₀ F₀ F₁ ⊗ₘ dgFunctorHomPre A E B D F₁ G₀ G₁) ≫
    dgFunctorComposition A D B (F₀.comp G₀) (F₁.comp G₀) (F₁.comp G₁)

/-- 横合成の元の全対象評価は、同じ後合成と同じ評価の縦合成。 -/
@[reassoc (attr := simp)]
lemma dgFunctorHorizontal_π (x : D) :
    dgFunctorHorizontal A D E B F₀ F₁ G₀ G₁ ≫
        dgFunctorHomπ A D B (F₀.comp G₀) (F₁.comp G₁) x =
      ((dgFunctorHomπ A D E F₀ F₁ x ≫ G₀.map (F₀.obj x) (F₁.obj x)) ⊗ₘ
        dgFunctorHomπ A E B G₀ G₁ (F₁.obj x)) ≫ eComp (Complex A) _ _ _ := by
  rw [dgFunctorHorizontal, Category.assoc, dgFunctorComposition_π,
    tensorHom_comp_tensorHom_assoc]
  simp only [dgFunctorHomPost_π, dgFunctorHomPre_π]
  rfl

/-- 逆の順に whisker する横合成。元の二パラメータは signed braiding で交換する。 -/
def dgFunctorHorizontalOther :
    dgFunctorHom A D E F₀ F₁ ⊗ dgFunctorHom A E B G₀ G₁ ⟶
      dgFunctorHom A D B (F₀.comp G₀) (F₁.comp G₁) :=
  (β_ (dgFunctorHom A D E F₀ F₁) (dgFunctorHom A E B G₀ G₁)).hom ≫
    (dgFunctorHomPre A E B D F₀ G₀ G₁ ⊗ₘ dgFunctorHomPost A D E B G₁ F₀ F₁) ≫
      dgFunctorComposition A D B (F₀.comp G₀) (F₀.comp G₁) (F₁.comp G₁)

/-- 二つの元の横合成は、全パラメータを保持して同じ Hom end の chain map に一致する。 -/
lemma dgFunctorHorizontal_eq_other :
    dgFunctorHorizontal A D E B F₀ F₁ G₀ G₁ =
      dgFunctorHorizontalOther A D E B F₀ F₁ G₀ G₁ := by
  apply dgFunctorHom_ext
  intro x
  rw [dgFunctorHorizontal_π]
  dsimp only [dgFunctorHorizontalOther]
  simp only [Category.assoc, dgFunctorComposition_π, tensorHom_comp_tensorHom_assoc,
    dgFunctorHomPre_π, dgFunctorHomPost_π]
  exact dgFunctorHorizontalNaturality A E B G₀ G₁ (F₀.obj x) (F₁.obj x)
    (dgFunctorHomπ A D E F₀ F₁ x)

end SerrePositivity.KST.SConstruction
