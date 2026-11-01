module

public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.ResolutionRowMixedMapping
public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.ResolutionBarReference

/-!
# 中断した任意モデル源への一般化：ResolutionBarRowPresentations

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：The actual resolution rows appear inside the existing framed bar。

## 方針（定義・証明）
frameによる導来写像空間と整合図式の厳密化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0297][inventory]を参照する。

[inventory]: ../../../../formalization-plans/k-theory-generalization-inventory.md#m0297
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# The actual resolution rows appear inside the existing framed bar

Each row augmentation gives an actual comma arrow from the reference.
Outer-frame lifts are chosen only for each individual arrow; no functorial
section or composition law for those choices is claimed.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory HomotopicalAlgebra Opposite

namespace SerrePositivity.HomotopyFunctionComplex.ResolutionBarRowPresentations
variable {C : Type u} [Category.{v} C] [ModelCategory C]
  (R : RightResolutionMapping.Index C) (n : SimplexCategoryᵒᵖ)

abbrev pair : RightResolutionMapping.Index C :=
  (op (FramedResolution.ofResolution (ResolutionFrameRows.row R.1.unop.inner n.unop)),
    op (FramedResolution.ofResolution (ResolutionFrameRows.row R.2.unop.inner n.unop)))

/-- Choose actual outer-frame lifts of the specified row augmentations. -/
def arrow : R ⟶ pair R n :=
  ((FramedResolution.lift (ResolutionFrameRows.augmentation R.1.unop.inner n.unop)).op,
    (FramedResolution.lift (ResolutionFrameRows.augmentation R.2.unop.inner n.unop)).op)

lemma arrow_base : (RightResolutionMapping.projection (C := C)).map (arrow R n) =
    𝟙 ((RightResolutionMapping.projection (C := C)).obj R) := rfl

lemma arrow_raw : (MixedBiresolutionComparison.functor (C := C)).map (arrow R n) =
    (ResolutionRowMixedMapping.rowComparison n).app R := rfl

abbrev comma : ResolutionBarCenters.Comma R := CostructuredArrow.mk (Y := pair R n) (𝟙 _)

def commaArrow : ResolutionBarReference.reference R ⟶ comma R n :=
  CostructuredArrow.homMk (arrow R n) (by
    change (RightResolutionMapping.projection (C := C)).map (arrow R n) ≫ 𝟙 _ = 𝟙 _
    rw [arrow_base, Category.id_comp]
    rfl)

abbrev element (m : SimplexCategoryᵒᵖ)
    (x : ((MixedBiresolutionComparison.functor (C := C)).obj R).obj m) :
    CostructuredArrow (SerrePositivity.SimplicialModel.BarConstruction.elementProjection
      (RightResolutionMapping.projection (C := C)) MixedBiresolutionComparison.functor m)
      ((RightResolutionMapping.projection (C := C)).obj R) :=
  CostructuredArrow.mk
    (Y := ((MixedBiresolutionComparison.functor (C := C)).flip.obj m).elementsMk (pair R n)
      (((ResolutionRowMixedMapping.rowComparison n).app R).app m x)) (𝟙 _)

/-- This is a morphism in the degreewise element comma category used by the bar itself. -/
def elementArrow (m : SimplexCategoryᵒᵖ)
    (x : ((MixedBiresolutionComparison.functor (C := C)).obj R).obj m) :
    ResolutionBarReference.point R m x ⟶ element R n m x :=
  CostructuredArrow.homMk (Functor.Elements.homMk (arrow R n) rfl) (by
    change (RightResolutionMapping.projection (C := C)).map (arrow R n) ≫ 𝟙 _ = 𝟙 _
    rw [arrow_base, Category.id_comp]
    rfl)

lemma elementArrow_underlying (m : SimplexCategoryᵒᵖ)
    (x : ((MixedBiresolutionComparison.functor (C := C)).obj R).obj m) :
    (elementArrow R n m x).left.hom = arrow R n := rfl

end SerrePositivity.HomotopyFunctionComplex.ResolutionBarRowPresentations
