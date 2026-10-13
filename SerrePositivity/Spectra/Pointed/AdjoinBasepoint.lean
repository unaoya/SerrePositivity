module

public import SerrePositivity.Spectra.Pointed.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts.BinaryProducts

/-!
# 自由な基点の追加

## 構成と普遍性

二項余積を持つ直積モノイダル圏で、X に終対象を別の成分として追加する。
その成分を基点にすると、基点を忘れる関手の左随伴となる。
smash 積の単位として用いる零次球面も、終対象に自由な基点を追加した対象として定義する。

## 注意

元の対象に基点を選ぶことと、自由な基点を追加することを区別する。
随伴は通常の圏について証明し、導来随伴やモデル構造を引用しない。
-/

@[expose] public section

universe v u

set_option backward.isDefEq.respectTransparency false

namespace SerrePositivity.PointedObject

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] [HasBinaryCoproducts C]

/-- 元の対象と終対象の余積の、第二成分を新しい基点にする。 -/
noncomputable def adjoin (X : C) : PointedObject C :=
  Under.mk (coprod.inr : 𝟙_ C ⟶ X ⨿ 𝟙_ C)

/-- 自由な基点の追加を関手にする。新しい成分では恒等写像を使う。 -/
noncomputable def adjoinFunctor : C ⥤ PointedObject C where
  obj X := adjoin X
  map f := Under.homMk (coprod.map f (𝟙 (𝟙_ C))) (by simp [adjoin])
  map_id X := by
    apply Under.UnderMorphism.ext
    simp [adjoin]
  map_comp f g := by
    apply Under.UnderMorphism.ext
    simp

/-- 新しい基点を付けた対象からの基点付き射は、元の対象からの任意の射と対応する。 -/
noncomputable def adjoinHomEquiv (X : C) (Y : PointedObject C) :
    (adjoin X ⟶ Y) ≃ (X ⟶ Y.right) where
  toFun f := coprod.inl ≫ f.right
  invFun f := Under.homMk (coprod.desc f Y.hom) (by simp [adjoin])
  left_inv f := by
    apply Under.UnderMorphism.ext
    apply coprod.hom_ext
    · simp
    · simpa [adjoin] using (Under.w f).symm
  right_inv f := by simp

/-- 自由な基点の追加は忘却関手の左随伴。
余積の普遍性に基づく Hom 同値の自然性も証明する。 -/
noncomputable def adjoinForgetAdjunction : adjoinFunctor (C := C) ⊣ forget :=
  Adjunction.mkOfHomEquiv {
    homEquiv := adjoinHomEquiv
    homEquiv_naturality_left_symm := fun f g ↦ by
      apply Under.UnderMorphism.ext
      apply coprod.hom_ext <;> simp [adjoinHomEquiv, adjoinFunctor]
    homEquiv_naturality_right := fun f g ↦ by
      simp [adjoinHomEquiv, Category.assoc] }

/-- 零次球面は、終対象に別の基点を付けた二つの点の対象。
閉直積圏での smash 積の単位同型は、`SmashUnit` で構成する。 -/
noncomputable def sphereZero : PointedObject C := adjoin (𝟙_ C)

end SerrePositivity.PointedObject
