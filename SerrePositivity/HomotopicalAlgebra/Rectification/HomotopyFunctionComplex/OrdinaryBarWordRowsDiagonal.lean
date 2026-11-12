module

public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarWordRows
public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarAmbientWordComparison

/-!
# 中断した任意モデル源への一般化：OrdinaryBarWordRowsDiagonal

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：The augmented row diagonal is the actual previously constructed word Hom。

## 方針（定義・証明）
自由単体的分解・Dwyer–Kan型の生成射による整合化に対応する技法。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0247][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0247
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# The augmented row diagonal is the actual previously constructed word Hom
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory
open SerrePositivity.SimplicialModel

namespace SerrePositivity.HomotopyFunctionComplex.OrdinaryBarWordRowsDiagonal
open OrdinaryBarFreeResolutionSeed OrdinaryBarWordRows OrdinaryBarWordRowMaps
variable (C : Type u) [Category.{v} C] (X Y : D C)

def comparisonIso : diagonal C X Y ≅ OrdinaryBarAmbientWordComparison.hom C X Y :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro n m θ
    apply ConcreteCategory.hom_ext
    intro f
    change (row C X Y m).map θ
        ((AmbientWords.map (OrdinaryBarFixedSource.literalMap C θ)
          (MonoidWithZeroHom.id (WordSegment.degree.{max u v} n))).map f) =
      (OrdinaryBarAmbientWordComparison.hom C X Y).map θ f
    rw [OrdinaryBarFixedRowWordHom.map_eq, OrdinaryBarAmbientWordComparison.map_eq]
    rfl)

def toSource : OrdinaryBarAmbientWordComparison.hom C X Y ⟶
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v} (OrdinaryBarSourceHom.hom C X Y) :=
  (comparisonIso C X Y).inv ≫ OrdinaryBarWordRows.toSource C X Y

lemma toSource_app (n : SimplexCategoryᵒᵖ)
    (f : (OrdinaryBarAmbientWordComparison.hom C X Y).obj n) :
    (toSource C X Y).app n f = ULift.up
      ((AmbientWords.augmentation (FreeGeneratorCategories.degree (D C) (n.unop.len + 1))
        (WordSegment.degree.{max u v} n)).map f) := by
  change (OrdinaryBarFixedRowWordHom.augmentation C n.unop.len X Y).app n f = _
  exact OrdinaryBarFixedRowWordHom.augmentation_app C n.unop.len X Y n f

lemma augmentation_factorization : OrdinaryBarAmbientWordComparison.augmentation C X Y =
    toSource C X Y ≫ OrdinaryBarSourceHom.augmentation C X Y := by
  ext n f
  change ULift.up ((OrdinaryBarFixedAugmentation.sourceProjection C n).map
      ((RetractWords.augmentation
        (FreeGeneratorCategories.degree (D C) (n.unop.len + 1))
          (WordSegment.degree.{max u v} n)).map
            ((AmbientWords.toRetract
              (FreeGeneratorCategories.degree (D C) (n.unop.len + 1))
                (WordSegment.degree.{max u v} n)).map f))) =
      ULift.up ((OrdinaryBarFixedAugmentation.sourceProjection C n).map
        (((toSource C X Y).app n f).down))
  rw [toSource_app]
  have h := congr($(AmbientWords.toRetract_augmentation
    (C := FreeGeneratorCategories.degree (D C) (n.unop.len + 1))
    (M := WordSegment.degree.{max u v} n)).map f)
  exact congrArg (fun g => ULift.up ((OrdinaryBarFixedAugmentation.sourceProjection C n).map g)) h

end SerrePositivity.HomotopyFunctionComplex.OrdinaryBarWordRowsDiagonal
