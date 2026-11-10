module

public import SerrePositivity.Spectra.Pointed.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.Tactic.CrossRefAttribute

/-!
# 基点へ潰す商の普遍性

## 構成

基礎圏の射 f : X → Y に対し、X を終対象へ潰す pushout に基点を付ける。
基点付きの行き先 Z への射は、Y → Z で f の像を基点へ送る射と対応する。
これは通常の商の構成であり、導来余ファイバーとは区別する。

## 用途

単体的集合の境界を潰して球面を定義するための一般的な基盤。
商の射と普遍性を定義し、対象の名前だけで境界を潰したことを仮定しない。
-/

@[expose] public section

universe v u

set_option backward.isDefEq.respectTransparency false

namespace SerrePositivity.PointedObject

open CategoryTheory CategoryTheory.Limits CategoryTheory.CartesianMonoidalCategory

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
  {X Y : C} (f : X ⟶ Y) [HasPushout f (toUnit X)]

/-- f の像を一つの基点へ潰す通常の商。 -/
@[kerodon 00VK]
noncomputable def cofiber : PointedObject C := Under.mk (pushout.inr f (toUnit X))

/-- 元の対象から商の基礎対象への射。 -/
@[kerodon 00VK]
noncomputable def cofiberQuotient : Y ⟶ (cofiber f).right := pushout.inl f (toUnit X)

/-- f の像は商の基点へ送られる。 -/
@[kerodon 00VK, reassoc (attr := simp)] lemma cofiberQuotient_condition :
    f ≫ cofiberQuotient f = toUnit X ≫ (cofiber f).hom := pushout.condition

/-- f の像を基点へ送る射は、基点付きの商からの射へ降りる。 -/
noncomputable def cofiberDesc (Z : PointedObject C) (g : Y ⟶ Z.right)
    (h : f ≫ g = toUnit X ≫ Z.hom) : cofiber f ⟶ Z :=
  Under.homMk (pushout.desc g Z.hom h) (by simp [cofiber])

/-- 商から降ろした射を元の対象へ引き戻すと、元の射になる。 -/
@[reassoc (attr := simp)] lemma cofiberQuotient_desc (Z : PointedObject C)
    (g : Y ⟶ Z.right) (h) : cofiberQuotient f ≫ (cofiberDesc f Z g h).right = g :=
  pushout.inl_desc ..

/-- 基点付き商から出る射は、商への射との合成で決まる。 -/
@[ext] lemma cofiber_hom_ext {Z : PointedObject C} (g h : cofiber f ⟶ Z)
    (w : cofiberQuotient f ≫ g.right = cofiberQuotient f ≫ h.right) : g = h := by
  apply Under.UnderMorphism.ext
  apply pushout.hom_ext
  · exact w
  · exact (Under.w g).trans (Under.w h).symm

/-- 基点へ潰す商の普遍性を Hom 集合の同値として表す。 -/
noncomputable def cofiberHomEquiv (Z : PointedObject C) :
    (cofiber f ⟶ Z) ≃ {g : Y ⟶ Z.right // f ≫ g = toUnit X ≫ Z.hom} where
  toFun g := ⟨cofiberQuotient f ≫ g.right, by
    rw [cofiberQuotient_condition_assoc, Under.w g]⟩
  invFun g := cofiberDesc f Z g.1 g.2
  left_inv g := cofiber_hom_ext f _ _ (by simp)
  right_inv g := Subtype.ext (by simp)

end SerrePositivity.PointedObject
