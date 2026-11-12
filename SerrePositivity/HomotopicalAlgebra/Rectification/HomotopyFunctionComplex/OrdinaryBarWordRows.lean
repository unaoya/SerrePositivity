module

public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarWordRowMaps
public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarSourceHom

/-!
# 中断した任意モデル源への一般化：OrdinaryBarWordRows

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：The augmented bisimplicial word Hom diagram, natural in every outer operator。

## 方針（定義・証明）
自由単体的分解・Dwyer–Kan型の生成射による整合化に対応する技法。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0246][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0246
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# The augmented bisimplicial word Hom diagram, natural in every outer operator
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory
open SerrePositivity.SimplicialModel

namespace SerrePositivity.HomotopyFunctionComplex.OrdinaryBarWordRows
open FreeGeneratorCategories OrdinaryBarFreeResolutionSeed OrdinaryBarFixedSource
open OrdinaryBarWordRowMaps
variable (C : Type u) [Category.{v} C] (X Y : D C)

def targetRows : SimplexCategoryᵒᵖ ⥤ SSet.{max u v} :=
  _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v} (OrdinaryBarSourceHom.hom C X Y) ⋙ Functor.const SimplexCategoryᵒᵖ

def augmentation : rows C X Y ⟶ targetRows C X Y where
  app n := OrdinaryBarFixedRowWordHom.augmentation C n.unop.len X Y
  naturality {n m} θ := by
    apply NatTrans.ext
    funext k
    apply ConcreteCategory.hom_ext
    intro f
    change (OrdinaryBarFixedRowWordHom.augmentation C m.unop.len X Y).app k
        ((AmbientWords.map (literalMap C θ)
          (MonoidWithZeroHom.id (WordSegment.degree.{max u v} k))).map f) =
      ULift.up ((literalMap C θ).map
        ((OrdinaryBarFixedRowWordHom.augmentation C n.unop.len X Y).app k f).down)
    rw [OrdinaryBarFixedRowWordHom.augmentation_app,
      OrdinaryBarFixedRowWordHom.augmentation_app]
    exact congrArg ULift.up (congr($(AmbientWords.map_augmentation (literalMap C θ)
      (MonoidWithZeroHom.id (WordSegment.degree.{max u v} k))).map f))

lemma localized_augmentation_app (n : SimplexCategoryᵒᵖ) :
    IsIso (AnodyneHomotopy.anodyneQ.map ((augmentation C X Y).app n)) :=
  OrdinaryBarFixedRowWordHom.localized_augmentation_isIso C n.unop.len X Y

def diagonal : SSet.{max u v} :=
  Functor.diag SimplexCategoryᵒᵖ ⋙ Functor.uncurry.obj (rows C X Y)

def targetDiagonal : SSet.{max u v} :=
  Functor.diag SimplexCategoryᵒᵖ ⋙ Functor.uncurry.obj (targetRows C X Y)

def diagonalAugmentation : diagonal C X Y ⟶ targetDiagonal C X Y :=
  CategoryTheory.Functor.whiskerLeft (Functor.diag SimplexCategoryᵒᵖ)
    (Functor.uncurry.map (augmentation C X Y))

def targetDiagonalIso : targetDiagonal C X Y ≅
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v} (OrdinaryBarSourceHom.hom C X Y) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro n m θ
    apply ConcreteCategory.hom_ext
    intro f
    rfl)

def toSource : diagonal C X Y ⟶ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v} (OrdinaryBarSourceHom.hom C X Y) :=
  diagonalAugmentation C X Y ≫ (targetDiagonalIso C X Y).hom

end SerrePositivity.HomotopyFunctionComplex.OrdinaryBarWordRows
