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

end SerrePositivity.PointedObject
