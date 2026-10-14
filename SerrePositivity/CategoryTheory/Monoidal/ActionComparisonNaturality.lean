module

public import SerrePositivity.CategoryTheory.Monoidal.ActionComparisonAdjunction

/-! # 随伴の比較のパラメータ自然性 -/

@[expose] public section

universe v u

noncomputable section

namespace SerrePositivity.ActionComparisonNaturality

open CategoryTheory

variable {C : Type u} [Category.{v} C]
  {L L' M M' R R' S S' : C ⥤ C}
  (a : L ⊣ R) (a' : L' ⊣ R') (b : M ⊣ S) (b' : M' ⊣ S')
  (e : L ≅ M) (e' : L' ≅ M')

/-- 二つの左随伴の比較の自然性に対応する、右随伴の比較の自然性の等式。 -/
def parameterLaw (q : ∀ Y, R'.obj Y ⟶ R.obj Y) (r : ∀ Y, S'.obj Y ⟶ S.obj Y)
    (Y : C) : Prop :=
  q Y ≫ (ActionComparisonAdjunction.rightIso a b e).hom.app Y =
    (ActionComparisonAdjunction.rightIso a' b' e').hom.app Y ≫ r Y

/-- 転置のパラメータ自然性と左随伴の比較の自然性は、右随伴の比較へ移る。 -/
lemma parameter (p : ∀ X, L.obj X ⟶ L'.obj X) (q : ∀ Y, R'.obj Y ⟶ R.obj Y)
    (t : ∀ X, M.obj X ⟶ M'.obj X) (r : ∀ Y, S'.obj Y ⟶ S.obj Y)
    (ha : ∀ X Y (f : L'.obj X ⟶ Y), a.homEquiv X Y (p X ≫ f) =
      a'.homEquiv X Y f ≫ q Y)
    (hb : ∀ X Y (f : M'.obj X ⟶ Y), b.homEquiv X Y (t X ≫ f) =
      b'.homEquiv X Y f ≫ r Y)
    (he : ∀ X, p X ≫ e'.hom.app X = e.hom.app X ≫ t X) (Y : C) :
    parameterLaw a a' b b' e e' q r Y := by
  let X := R'.obj Y
  let f : M'.obj X ⟶ Y := e'.inv.app X ≫ (a'.homEquiv X Y).symm (𝟙 X)
  have hf : a'.homEquiv X Y (e'.hom.app X ≫ f) = 𝟙 X := by
    simp only [f, ← Category.assoc, Iso.hom_inv_id_app, Category.id_comp,
      Equiv.apply_symm_apply]
  have hi := ActionComparisonAdjunction.rightIso_homEquiv a' b' e' X Y f
  change a'.homEquiv X Y (e'.hom.app X ≫ f) ≫
    (ActionComparisonAdjunction.rightIso a' b' e').hom.app Y = b'.homEquiv X Y f at hi
  rw [hf, Category.id_comp] at hi
  have hp := ha X Y (e'.hom.app X ≫ f)
  rw [hf, Category.id_comp] at hp
  change q Y ≫ (ActionComparisonAdjunction.rightIso a b e).hom.app Y = _
  rw [← hp]
  calc
    _ = a.homEquiv X Y (e.hom.app X ≫ t X ≫ f) ≫
        (ActionComparisonAdjunction.rightIso a b e).hom.app Y := by
      rw [← Category.assoc, he, Category.assoc]
    _ = b.homEquiv X Y (t X ≫ f) :=
      ActionComparisonAdjunction.rightIso_homEquiv a b e X Y (t X ≫ f)
    _ = b'.homEquiv X Y f ≫ r Y := hb X Y f
    _ = _ := by rw [← hi]

section Composite

variable {L₁ L₁' L₂ L₂' R₁ R₁' R₂ R₂' : C ⥤ C}
  (a₁ : L₁ ⊣ R₁) (a₁' : L₁' ⊣ R₁') (a₂ : L₂ ⊣ R₂) (a₂' : L₂' ⊣ R₂')
  (p₁ : L₁ ⟶ L₁') (p₂ : L₂ ⟶ L₂') (q₁ : R₁' ⟶ R₁) (q₂ : R₂' ⟶ R₂)

/-- 二段の合成随伴の転置のパラメータ自然性の等式。 -/
def compositePreLaw (X Y : C) (f : L₂'.obj (L₁'.obj X) ⟶ Y) : Prop :=
  (a₁.comp a₂).homEquiv X Y (p₂.app (L₁.obj X) ≫ L₂'.map (p₁.app X) ≫ f) =
    (a₁'.comp a₂').homEquiv X Y f ≫ R₁'.map (q₂.app Y) ≫ q₁.app (R₂.obj Y)

/-- 各転置の自然性と右随伴の前合成の自然性から、反復転置の自然性を得る。 -/
lemma composite_pre
    (h₁ : ∀ X Y (f : L₁'.obj X ⟶ Y), a₁.homEquiv X Y (p₁.app X ≫ f) =
      a₁'.homEquiv X Y f ≫ q₁.app Y)
    (h₂ : ∀ X Y (f : L₂'.obj X ⟶ Y), a₂.homEquiv X Y (p₂.app X ≫ f) =
      a₂'.homEquiv X Y f ≫ q₂.app Y)
    (X Y : C) (f : L₂'.obj (L₁'.obj X) ⟶ Y) :
    compositePreLaw a₁ a₁' a₂ a₂' p₁ p₂ q₁ q₂ X Y f := by
  unfold compositePreLaw
  rw [Adjunction.comp_homEquiv, Adjunction.comp_homEquiv]
  change a₁.homEquiv X (R₂.obj Y)
    (a₂.homEquiv (L₁.obj X) Y (p₂.app (L₁.obj X) ≫ L₂'.map (p₁.app X) ≫ f)) = _
  rw [h₂, a₂'.homEquiv_naturality_left, a₁.homEquiv_naturality_right, h₁,
    Category.assoc, ← q₁.naturality]
  rfl

variable {A A' B B' : C ⥤ C} (c : A ⊣ B) (c' : A' ⊣ B')
  (d : A ≅ L₁ ⋙ L₂) (d' : A' ≅ L₁' ⋙ L₂')

/-- 合成随伴の転置の法則を使い、反復右随伴の比較の自然性を得る。 -/
lemma parameter_composite (p : ∀ X, A.obj X ⟶ A'.obj X)
    (q : ∀ Y, B'.obj Y ⟶ B.obj Y)
    (hc : ∀ X Y (f : A'.obj X ⟶ Y), c.homEquiv X Y (p X ≫ f) =
      c'.homEquiv X Y f ≫ q Y)
    (hcomp : ∀ X Y (f : L₂'.obj (L₁'.obj X) ⟶ Y),
      compositePreLaw a₁ a₁' a₂ a₂' p₁ p₂ q₁ q₂ X Y f)
    (hd : ∀ X, p X ≫ d'.hom.app X = d.hom.app X ≫
      p₂.app (L₁.obj X) ≫ L₂'.map (p₁.app X)) (Y : C) :
    parameterLaw c c' (a₁.comp a₂) (a₁'.comp a₂') d d' q
      (fun Y => R₁'.map (q₂.app Y) ≫ q₁.app (R₂.obj Y)) Y :=
  parameter c c' (a₁.comp a₂) (a₁'.comp a₂') d d' p q
    (fun X => p₂.app (L₁.obj X) ≫ L₂'.map (p₁.app X))
    (fun Y => R₁'.map (q₂.app Y) ≫ q₁.app (R₂.obj Y))
    hc (fun X Y f => by
      simpa only [compositePreLaw, Category.assoc] using hcomp X Y f) hd Y

end Composite

end SerrePositivity.ActionComparisonNaturality
