module

public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarFixedAugmentation
public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarDiagonalHomAugmentation

/-!
# 中断した任意モデル源への一般化：OrdinaryBarSourceHom

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：The actual outer source Hom simplicial set and its base augmentation。

## 方針（定義・証明）
frameによる導来写像空間と整合図式の厳密化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0227][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0227
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# The actual outer source Hom simplicial set and its base augmentation
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory
open SerrePositivity.SimplicialModel

namespace SerrePositivity.HomotopyFunctionComplex.OrdinaryBarSourceHom
open FreeGeneratorCategories OrdinaryBarFreeResolutionSeed OrdinaryBarFixedSource
variable (C : Type u) [Category.{v} C] (X Y : D C)

def hom : SSet.{max u v} where
  obj n := @Quiver.Hom ((diagram C).obj n) ((diagram C).obj n).str.toQuiver X Y
  map θ := ↾fun f => (literalMap C θ).map f
  map_id n := by
    apply ConcreteCategory.hom_ext
    intro f
    have h := congrArg Cat.Hom.toFunctor ((literal C).map_id n)
    exact congr($(h).map f)
  map_comp θ φ := by
    apply ConcreteCategory.hom_ext
    intro f
    have h := congrArg Cat.Hom.toFunctor ((literal C).map_comp θ φ)
    exact congr($(h).map f)

def augmentation : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v} (hom C X Y) ⟶
    OrdinaryBarDiagonalHomAugmentation.baseHom C X Y where
  app n := ↾fun f => ULift.up ((OrdinaryBarFixedAugmentation.sourceProjection C n).map f.down)
  naturality {_ _} θ := by
    apply ConcreteCategory.hom_ext
    intro f
    have h := congr($(OrdinaryBarFixedAugmentation.sourceProjection_naturality C θ).map f.down)
    exact congrArg ULift.up h

end SerrePositivity.HomotopyFunctionComplex.OrdinaryBarSourceHom
