module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryResolutionPairs
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionRowMixedMapping

/-!
# 中断した任意モデル源への一般化：OrdinaryResolutionRows

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：All original frame rows form a strict diagram inside the ordinary resolution comma category。

## 方針（定義・証明）
frameによる導来写像空間と整合図式の厳密化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0256][inventory]を参照する。

[inventory]: ../../../formalization-plans/k-theory-generalization-inventory.md#m0256
[plan]: ../../../formalization-plans/k-theory.md
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# All original frame rows form a strict diagram inside the ordinary resolution comma category

No new outer-frame lift is selected for a row operator. The raw values and
augmentation maps are exactly the existing mixed row diagram.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory HomotopicalAlgebra Opposite

namespace SerrePositivity.HomotopyFunctionComplex.OrdinaryResolutionRows
variable {C : Type u} [Category.{v} C] [ModelCategory C]
  (R : RightResolutionMapping.Index C)

abbrev rows : SimplexCategoryᵒᵖ ⥤ OrdinaryResolutionPairs.Index (C := C) :=
  (ResolutionFrameRows.functor R.1.unop.inner).op.prod'
    (ResolutionFrameRows.functor R.2.unop.inner).op

lemma projection_eq : rows R ⋙ OrdinaryResolutionPairs.projection =
    (Functor.const SimplexCategoryᵒᵖ).obj
      ((RightResolutionMapping.projection (C := C)).obj R) := rfl

lemma raw_eq : rows R ⋙ OrdinaryResolutionPairs.raw =
    (ResolutionRowMixedMapping.rows (C := C)).flip.obj R := rfl

abbrev augmentation : (Functor.const SimplexCategoryᵒᵖ).obj
    ((OrdinaryResolutionPairs.forgetFrames (C := C)).obj R) ⟶ rows R :=
  NatTrans.prod' (NatTrans.op (ResolutionFrameRows.comparison R.1.unop.inner))
    (NatTrans.op (ResolutionFrameRows.comparison R.2.unop.inner))

lemma raw_augmentation (n : SimplexCategoryᵒᵖ) :
    (OrdinaryResolutionPairs.raw (C := C)).map ((augmentation R).app n) =
      (ResolutionRowMixedMapping.rowComparison n).app R := rfl

abbrev Comma := CostructuredArrow (OrdinaryResolutionPairs.projection (C := C))
  ((RightResolutionMapping.projection (C := C)).obj R)

def commaRows : SimplexCategoryᵒᵖ ⥤ Comma R where
  obj n := CostructuredArrow.mk (Y := (rows R).obj n) (𝟙 _)
  map θ := CostructuredArrow.homMk ((rows R).map θ) (by
    change 𝟙 ((RightResolutionMapping.projection (C := C)).obj R) ≫
      𝟙 ((RightResolutionMapping.projection (C := C)).obj R) =
        𝟙 ((RightResolutionMapping.projection (C := C)).obj R)
    exact Category.id_comp _)
  map_id n := by
    apply CostructuredArrow.hom_ext
    exact (rows R).map_id n
  map_comp θ σ := by
    apply CostructuredArrow.hom_ext
    exact (rows R).map_comp θ σ

abbrev reference : Comma R :=
  CostructuredArrow.mk (Y := (OrdinaryResolutionPairs.forgetFrames (C := C)).obj R) (𝟙 _)

def commaAugmentation : (Functor.const SimplexCategoryᵒᵖ).obj (reference R) ⟶ commaRows R where
  app n := CostructuredArrow.homMk ((augmentation R).app n) (by
    change (OrdinaryResolutionPairs.projection (C := C)).map ((augmentation R).app n) ≫ 𝟙 _ = 𝟙 _
    change 𝟙 _ ≫ 𝟙 _ = 𝟙 _
    exact Category.id_comp _)
  naturality {n m} θ := by
    apply CostructuredArrow.hom_ext
    exact (augmentation R).naturality θ

variable [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)

include hcof hfib in
lemma raw_augmentation_weakEquivalence (n : SimplexCategoryᵒᵖ) :
    weakEquivalences SSet.{v}
      ((OrdinaryResolutionPairs.raw (C := C)).map ((augmentation R).app n)) :=
  ResolutionRowMixedMapping.rowComparison_weakEquivalence hcof hfib R n

end SerrePositivity.HomotopyFunctionComplex.OrdinaryResolutionRows
