module

public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarSourceExtraDegeneracy
public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarWordDiagonalEquivalence
public import SerrePositivity.HomotopicalAlgebra.Simplicial.OppositeHomotopy

/-!
# 中断した任意モデル源への一般化：OrdinaryBarSourceContraction

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：The actual source and small-vertex augmentations are localized isomorphisms。

## 方針（定義・証明）
frameによる導来写像空間と整合図式の厳密化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0224][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0224
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# The actual source and small-vertex augmentations are localized isomorphisms
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory
open SerrePositivity.SimplicialModel

namespace SerrePositivity.HomotopyFunctionComplex.OrdinaryBarSourceContraction
open OrdinaryBarFreeResolutionSeed OppositeHomotopy
variable (C : Type u) [Category.{v} C] (X Y : D C)

abbrev baseReverseIso : reverse (OrdinaryBarDiagonalHomAugmentation.baseHom C X Y) ≅
    OrdinaryBarDiagonalHomAugmentation.baseHom C X Y :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by intro n m θ; rfl)

lemma augmentation_factorization : OrdinaryBarSourceHom.augmentation C X Y =
    (doubleIso (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v} (OrdinaryBarSourceHom.hom C X Y))).inv ≫
      reverseMap (OrdinaryBarSourceExtraDegeneracy.augmented C X Y).hom ≫
        (baseReverseIso C X Y).hom := by
  ext n f
  rfl

lemma source_augmentation_isIso : IsIso (AnodyneHomotopy.anodyneQ.map
    (OrdinaryBarSourceHom.augmentation C X Y)) := by
  have := localized_reversed_augmentation_isIso
    (OrdinaryBarSourceExtraDegeneracy.extraDegeneracy C X Y)
  rw [augmentation_factorization]
  simp only [AnodyneHomotopy.anodyneQ.map_comp]
  infer_instance

lemma word_augmentation_isIso : IsIso (AnodyneHomotopy.anodyneQ.map
    (OrdinaryBarAmbientWordComparison.augmentation C X Y)) :=
  (OrdinaryBarWordDiagonalEquivalence.augmentation_isIso_iff_source C X Y).mpr
    (source_augmentation_isIso C X Y)

lemma small_augmentation_isIso : IsIso (AnodyneHomotopy.anodyneQ.map
    (OrdinaryBarDiagonalHomAugmentation.smallAugmentation C X Y)) :=
  (OrdinaryBarWordDiagonalEquivalence.small_augmentation_isIso_iff_source C X Y).mpr
    (source_augmentation_isIso C X Y)

end SerrePositivity.HomotopyFunctionComplex.OrdinaryBarSourceContraction
