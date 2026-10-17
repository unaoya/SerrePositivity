module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionFrameRows

/-!
# 中断した任意モデル源への一般化：ResolutionFrameRowFunctor

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：The actual row resolutions are functorial in framed comparison maps。

## 方針（定義・証明）
frameによる導来写像空間と整合図式の厳密化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0303][inventory]を参照する。

[inventory]: ../../../formalization-plans/k-theory-generalization-inventory.md#m0303
[plan]: ../../../formalization-plans/k-theory.md
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# The actual row resolutions are functorial in framed comparison maps

The target category is the ordinary resolution category. No functorial
choice of outer-frame lifts for the new row resolutions is asserted.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory HomotopicalAlgebra

namespace SerrePositivity.HomotopyFunctionComplex.ResolutionFrameRowFunctor
variable {C : Type u} [Category.{v} C] [ModelCategory C]
local instance : ModelCategory (SimplexCategory ⥤ C) := Reedy.simplexModelCategory C

def component {X Y : FramedResolution C} (f : X ⟶ Y) (n : SimplexCategory) :
    ResolutionFrameRows.row X.inner n ⟶ ResolutionFrameRows.row Y.inner n where
  base := f.map.base
  diagram := f.frame.app n
  over := by
    change f.frame.app n ≫ (_ ≫ Y.inner.resolution.augmentation) =
      (_ ≫ X.inner.resolution.augmentation) ≫ (Functor.const SimplexCategory).map f.map.base
    have h := congr_app f.over n
    change f.frame.app n ≫ (ResolutionLiftSpace.frame Y.inner).augmentation.app n =
      (ResolutionLiftSpace.frame X.inner).augmentation.app n ≫ f.map.diagram at h
    rw [← Category.assoc, h, Category.assoc, f.map.over, ← Category.assoc]

def map {X Y : FramedResolution C} (f : X ⟶ Y) :
    ResolutionFrameRows.functor X.inner ⟶ ResolutionFrameRows.functor Y.inner where
  app := component f
  naturality {n m} θ := by
    apply ResolutionObject.Hom.ext
    · change 𝟙 _ ≫ f.map.base = f.map.base ≫ 𝟙 _
      simp only [Category.id_comp, Category.comp_id]
    · exact f.frame.naturality θ

def functor : FramedResolution C ⥤ SimplexCategory ⥤ ResolutionObject C where
  obj X := ResolutionFrameRows.functor X.inner
  map f := map f
  map_id X := by
    apply NatTrans.ext
    funext n
    apply ResolutionObject.Hom.ext <;> rfl
  map_comp f g := by
    apply NatTrans.ext
    funext n
    apply ResolutionObject.Hom.ext <;> rfl

abbrev constant : FramedResolution C ⥤ SimplexCategory ⥤ ResolutionObject C :=
  FramedResolution.forget ⋙ Functor.const SimplexCategory

def comparison : functor (C := C) ⟶ constant where
  app X := ResolutionFrameRows.comparison X.inner
  naturality {X Y} f := by
    apply NatTrans.ext
    funext n
    apply ResolutionObject.Hom.ext
    · change f.map.base ≫ 𝟙 _ = 𝟙 _ ≫ f.map.base
      simp only [Category.id_comp, Category.comp_id]
    · exact congr_app f.over n

abbrev atDegree (n : SimplexCategory) : FramedResolution C ⥤ ResolutionObject C :=
  functor ⋙ (evaluation SimplexCategory (ResolutionObject C)).obj n

end SerrePositivity.HomotopyFunctionComplex.ResolutionFrameRowFunctor
