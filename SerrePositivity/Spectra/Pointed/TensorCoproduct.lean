module

public import SerrePositivity.Spectra.Pointed.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Braided
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts

/-!
# 直積による余積の保存

閉直積モノイダル圏では、各対象との直積は左随伴となる。
そのため二項余積を保存し、余積との直積から出る射を二つの成分で構成・判定できる。
smash 積の単位と結合性で必要な保存条件を、閉構造から供給するための一般論。
単体的集合での閉構造への接続は別モジュールで確認する。
-/

@[expose] public section

universe v u

set_option backward.isDefEq.respectTransparency false

namespace SerrePositivity.PointedObject

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
  [MonoidalClosed C] [HasBinaryCoproducts C]

attribute [local instance] BraidedCategory.ofCartesianMonoidalCategory

/-- 余積との直積は、直積した各成分の余積となる。
閉構造による左随伴性と、余積の保存の標準比較を使う。 -/
noncomputable def tensorRightCoprodIsColimit (A B X : C) :
    IsColimit (BinaryCofan.mk ((coprod.inl : A ⟶ A ⨿ B) ▷ X)
      ((coprod.inr : B ⟶ A ⨿ B) ▷ X)) :=
  isColimitOfHasBinaryCoproductOfPreservesColimit (tensorRight X) A B

/-- 余積との直積から出る射を、二つの成分から作る。 -/
noncomputable def tensorRightDesc {A B X Y : C} (f : A ⊗ X ⟶ Y) (g : B ⊗ X ⟶ Y) :
    (A ⨿ B) ⊗ X ⟶ Y :=
  (tensorRightCoprodIsColimit A B X).desc (BinaryCofan.mk f g)

@[reassoc (attr := simp)] lemma tensorRightDesc_inl {A B X Y : C}
    (f : A ⊗ X ⟶ Y) (g : B ⊗ X ⟶ Y) :
    (coprod.inl ▷ X) ≫ tensorRightDesc f g = f :=
  (tensorRightCoprodIsColimit A B X).fac (BinaryCofan.mk f g) ⟨WalkingPair.left⟩

@[reassoc (attr := simp)] lemma tensorRightDesc_inr {A B X Y : C}
    (f : A ⊗ X ⟶ Y) (g : B ⊗ X ⟶ Y) :
    (coprod.inr ▷ X) ≫ tensorRightDesc f g = g :=
  (tensorRightCoprodIsColimit A B X).fac (BinaryCofan.mk f g) ⟨WalkingPair.right⟩

/-- 余積との直積から出る射は、二つの成分上で決まる。 -/
lemma tensorRightCoprod_hom_ext {A B X Y : C} (f g : (A ⨿ B) ⊗ X ⟶ Y)
    (h₁ : (coprod.inl ▷ X) ≫ f = (coprod.inl ▷ X) ≫ g)
    (h₂ : (coprod.inr ▷ X) ≫ f = (coprod.inr ▷ X) ≫ g) : f = g :=
  BinaryCofan.IsColimit.hom_ext (tensorRightCoprodIsColimit A B X) h₁ h₂

/-- 左側の固定対象との直積も二項余積を保存する。 -/
noncomputable def tensorLeftCoprodIsColimit (X A B : C) :
    IsColimit (BinaryCofan.mk (X ◁ (coprod.inl : A ⟶ A ⨿ B))
      (X ◁ (coprod.inr : B ⟶ A ⨿ B))) :=
  isColimitOfHasBinaryCoproductOfPreservesColimit (tensorLeft X) A B

/-- 第二因子の余積から出る射を二成分で構成する。 -/
noncomputable def tensorLeftDesc {X A B Y : C} (f : X ⊗ A ⟶ Y) (g : X ⊗ B ⟶ Y) :
    X ⊗ (A ⨿ B) ⟶ Y :=
  (tensorLeftCoprodIsColimit X A B).desc (BinaryCofan.mk f g)

@[reassoc (attr := simp)] lemma tensorLeftDesc_inl {X A B Y : C}
    (f : X ⊗ A ⟶ Y) (g : X ⊗ B ⟶ Y) :
    (X ◁ coprod.inl) ≫ tensorLeftDesc f g = f :=
  (tensorLeftCoprodIsColimit X A B).fac (BinaryCofan.mk f g) ⟨WalkingPair.left⟩

@[reassoc (attr := simp)] lemma tensorLeftDesc_inr {X A B Y : C}
    (f : X ⊗ A ⟶ Y) (g : X ⊗ B ⟶ Y) :
    (X ◁ coprod.inr) ≫ tensorLeftDesc f g = g :=
  (tensorLeftCoprodIsColimit X A B).fac (BinaryCofan.mk f g) ⟨WalkingPair.right⟩

/-- 第二因子が余積の直積から出る射は、二成分上で決まる。 -/
lemma tensorLeftCoprod_hom_ext {X A B Y : C} (f g : X ⊗ (A ⨿ B) ⟶ Y)
    (h₁ : (X ◁ coprod.inl) ≫ f = (X ◁ coprod.inl) ≫ g)
    (h₂ : (X ◁ coprod.inr) ≫ f = (X ◁ coprod.inr) ≫ g) : f = g :=
  BinaryCofan.IsColimit.hom_ext (tensorLeftCoprodIsColimit X A B) h₁ h₂

/-- 二つの余積の直積から出る射を四成分で構成する。 -/
noncomputable def tensorCoprodDesc {A B X Y Z : C}
    (f₁₁ : A ⊗ X ⟶ Z) (f₁₂ : A ⊗ Y ⟶ Z)
    (f₂₁ : B ⊗ X ⟶ Z) (f₂₂ : B ⊗ Y ⟶ Z) : (A ⨿ B) ⊗ (X ⨿ Y) ⟶ Z :=
  tensorRightDesc (tensorLeftDesc f₁₁ f₁₂) (tensorLeftDesc f₂₁ f₂₂)

@[reassoc (attr := simp)] lemma tensorCoprodDesc_inl_inl {A B X Y Z : C}
    (f₁₁ : A ⊗ X ⟶ Z) (f₁₂ : A ⊗ Y ⟶ Z)
    (f₂₁ : B ⊗ X ⟶ Z) (f₂₂ : B ⊗ Y ⟶ Z) :
    (coprod.inl ⊗ₘ coprod.inl) ≫ tensorCoprodDesc f₁₁ f₁₂ f₂₁ f₂₂ = f₁₁ := by
  simp [tensorCoprodDesc, tensorHom_def', Category.assoc]

@[reassoc (attr := simp)] lemma tensorCoprodDesc_inl_inr {A B X Y Z : C}
    (f₁₁ : A ⊗ X ⟶ Z) (f₁₂ : A ⊗ Y ⟶ Z)
    (f₂₁ : B ⊗ X ⟶ Z) (f₂₂ : B ⊗ Y ⟶ Z) :
    (coprod.inl ⊗ₘ coprod.inr) ≫ tensorCoprodDesc f₁₁ f₁₂ f₂₁ f₂₂ = f₁₂ := by
  simp [tensorCoprodDesc, tensorHom_def', Category.assoc]

@[reassoc (attr := simp)] lemma tensorCoprodDesc_inr_inl {A B X Y Z : C}
    (f₁₁ : A ⊗ X ⟶ Z) (f₁₂ : A ⊗ Y ⟶ Z)
    (f₂₁ : B ⊗ X ⟶ Z) (f₂₂ : B ⊗ Y ⟶ Z) :
    (coprod.inr ⊗ₘ coprod.inl) ≫ tensorCoprodDesc f₁₁ f₁₂ f₂₁ f₂₂ = f₂₁ := by
  simp [tensorCoprodDesc, tensorHom_def', Category.assoc]

@[reassoc (attr := simp)] lemma tensorCoprodDesc_inr_inr {A B X Y Z : C}
    (f₁₁ : A ⊗ X ⟶ Z) (f₁₂ : A ⊗ Y ⟶ Z)
    (f₂₁ : B ⊗ X ⟶ Z) (f₂₂ : B ⊗ Y ⟶ Z) :
    (coprod.inr ⊗ₘ coprod.inr) ≫ tensorCoprodDesc f₁₁ f₁₂ f₂₁ f₂₂ = f₂₂ := by
  simp [tensorCoprodDesc, tensorHom_def', Category.assoc]

/-- 二つの余積の直積から出る射は、四成分上で決まる。 -/
lemma tensorCoprod_hom_ext {A B X Y Z : C} (f g : (A ⨿ B) ⊗ (X ⨿ Y) ⟶ Z)
    (h₁₁ : (coprod.inl ⊗ₘ coprod.inl) ≫ f = (coprod.inl ⊗ₘ coprod.inl) ≫ g)
    (h₁₂ : (coprod.inl ⊗ₘ coprod.inr) ≫ f = (coprod.inl ⊗ₘ coprod.inr) ≫ g)
    (h₂₁ : (coprod.inr ⊗ₘ coprod.inl) ≫ f = (coprod.inr ⊗ₘ coprod.inl) ≫ g)
    (h₂₂ : (coprod.inr ⊗ₘ coprod.inr) ≫ f = (coprod.inr ⊗ₘ coprod.inr) ≫ g) : f = g := by
  apply tensorRightCoprod_hom_ext
  · apply tensorLeftCoprod_hom_ext
    · simpa only [tensorHom_def', Category.assoc] using h₁₁
    · simpa only [tensorHom_def', Category.assoc] using h₁₂
  · apply tensorLeftCoprod_hom_ext
    · simpa only [tensorHom_def', Category.assoc] using h₂₁
    · simpa only [tensorHom_def', Category.assoc] using h₂₂

end SerrePositivity.PointedObject
