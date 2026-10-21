module
public import Mathlib.CategoryTheory.Monoidal.Comon_

/-! # 余モノイドの忘却関手による構造射の回収
概要：余モノイド圏の結合子・左右単位子の underlying 射を回収する。
方針：標準の強モノイダル忘却関手の構造射が恒等射であることを使う。
規約：任意の braided 圏で証明する。使われ方：Serre 余モノイドの coherent 法則の反映。
-/
@[expose] public section
universe v u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]

/-- 元の余モノイド tensor 単位の underlying 対象は同じ tensor 単位。 -/
lemma comonoidForget_unitObj : (𝟙_ (Comon C)).X = 𝟙_ C := rfl

/-- 元の余モノイド結合子を忘却すると underlying 圏の結合子となる。 -/
lemma comonoidForget_associator (X Y Z : Comon C) :
    (α_ X Y Z).hom.hom = (α_ X.X Y.X Z.X).hom := by
  have h := Functor.Monoidal.map_associator (Comon.forget C) X Y Z
  simp only [Comon.forget_δ, Comon.forget_μ] at h
  change (α_ X Y Z).hom.hom = 𝟙 _ ≫ 𝟙 _ ▷ Z.X ≫
    (α_ X.X Y.X Z.X).hom ≫ X.X ◁ 𝟙 _ ≫ 𝟙 _ at h
  simpa only [id_whiskerRight, whiskerLeft_id, Category.id_comp,
    Category.comp_id] using h

/-- 元の余モノイド左単位子を忘却すると underlying 圏の左単位子となる。 -/
lemma comonoidForget_leftUnitor (X : Comon C) :
    (λ_ X).hom.hom = (λ_ X.X).hom := by
  have h := Functor.Monoidal.map_leftUnitor (Comon.forget C) X
  simp only [Comon.forget_δ, Comon.forget_η] at h
  change (λ_ X).hom.hom = 𝟙 _ ≫ 𝟙 _ ▷ X.X ≫ (λ_ X.X).hom at h
  simpa only [id_whiskerRight, Category.id_comp] using h

/-- 元の余モノイド右単位子を忘却すると underlying 圏の右単位子となる。 -/
lemma comonoidForget_rightUnitor (X : Comon C) :
    (ρ_ X).hom.hom = (ρ_ X.X).hom := by
  have h := Functor.Monoidal.map_rightUnitor (Comon.forget C) X
  simp only [Comon.forget_δ, Comon.forget_η] at h
  change (ρ_ X).hom.hom = 𝟙 _ ≫ X.X ◁ 𝟙 _ ≫ (ρ_ X.X).hom at h
  simpa only [whiskerLeft_id, Category.id_comp] using h

end SerrePositivity.KST.SConstruction
