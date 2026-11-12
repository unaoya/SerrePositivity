module

public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarSourceSection

/-!
# 中断した任意モデル源への一般化：OrdinaryBarSourceWordEmbedding

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：The actual source Hom maps into ambient and small-vertex word Hom。

## 方針（定義・証明）
自由単体的分解・Dwyer–Kan型の生成射による整合化に対応する技法。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0230][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0230
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# The actual source Hom maps into ambient and small-vertex word Hom

All simplicial operators and the original augmentations commute. The
small-vertex map sandwiches by the retract maps and is not claimed to
preserve composition.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory
open SerrePositivity.SimplicialModel

namespace SerrePositivity.HomotopyFunctionComplex.OrdinaryBarSourceWordEmbedding
open FreeGeneratorCategories OrdinaryBarFreeResolutionSeed OrdinaryBarFixedWordResolution
open OrdinaryBarDiagonalAmbientHom OrdinaryBarDiagonalHomAugmentation
variable (C : Type u) [Category.{v} C] (X Y : D C)

def ambient : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v} (OrdinaryBarSourceHom.hom C X Y) ⟶
    ambientHom C X Y where
  app n := ↾fun f => (RetractWords.sourceFunctor (degree (D C) (n.unop.len + 1))
    (WordSegment.degree.{max u v} n)).map f.down
  naturality {n m} θ := by
    apply ConcreteCategory.hom_ext
    intro f
    change (RetractWords.sourceFunctor (degree (D C) (m.unop.len + 1))
        (WordSegment.degree.{max u v} m)).map
          ((OrdinaryBarFixedSource.literalMap C θ).map f.down) =
      (RetractWords.map (𝟭 (degree (D C) (m.unop.len + 1))) (WordSegment.degreeMap θ)).map
        ((RetractWords.map (OrdinaryBarFixedSource.literalMap C θ)
          (MonoidWithZeroHom.id _)).map
            ((RetractWords.sourceFunctor (degree (D C) (n.unop.len + 1))
              (WordSegment.degree.{max u v} n)).map f.down))
    have h₁ := RetractWords.map_source
      (C := degree (D C) (n.unop.len + 1))
      (OrdinaryBarFixedSource.literalMap C θ)
      (MonoidWithZeroHom.id (WordSegment.degree.{max u v} n)) f.down
    have h₂ := RetractWords.map_source
      (C := degree (D C) (m.unop.len + 1)) (𝟭 _) (WordSegment.degreeMap θ)
      ((OrdinaryBarFixedSource.literalMap C θ).map f.down)
    exact ((congrArg ((RetractWords.map (𝟭 (degree (D C) (m.unop.len + 1)))
      (WordSegment.degreeMap θ)).map) h₁).trans h₂).symm


lemma ambient_augmentation : ambient C X Y ≫ ambientAugmentation C X Y =
    OrdinaryBarSourceHom.augmentation C X Y := by
  ext n f
  change ULift.up ((OrdinaryBarFixedAugmentation.sourceProjection C n).map
      ((RetractWords.augmentation _ _).map
        ((RetractWords.quotient _ _).map (RetractWords.source _ _ f.down)))) = _
  rw [RetractWords.augmentation_source]
  rfl

def small : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v} (OrdinaryBarSourceHom.hom C X Y) ⟶ hom C X Y :=
  ambient C X Y ≫ transfer C X Y

lemma small_augmentation : small C X Y ≫ smallAugmentation C X Y =
    OrdinaryBarSourceHom.augmentation C X Y := by
  rw [small, Category.assoc, transfer_augmentation, ambient_augmentation]

lemma ambient_isIso : IsIso (AnodyneHomotopy.anodyneQ.map (ambient C X Y)) := by
  have : IsIso (AnodyneHomotopy.anodyneQ.map (ambientAugmentation C X Y)) :=
    (localized_small_iff_ambient C X Y).mp
      (OrdinaryBarSourceContraction.small_augmentation_isIso C X Y)
  have h := congrArg AnodyneHomotopy.anodyneQ.map (ambient_augmentation C X Y)
  rw [Functor.map_comp] at h
  have : IsIso (AnodyneHomotopy.anodyneQ.map (ambient C X Y) ≫
      AnodyneHomotopy.anodyneQ.map (ambientAugmentation C X Y)) :=
    h.symm ▸ OrdinaryBarSourceContraction.source_augmentation_isIso C X Y
  exact (isIso_comp_right_iff _ _).mp this

lemma small_isIso : IsIso (AnodyneHomotopy.anodyneQ.map (small C X Y)) := by
  have := ambient_isIso C X Y
  have := OrdinaryBarDiagonalHomRetraction.localized_transfer_isIso C X Y
  rw [small, Functor.map_comp]
  infer_instance

end SerrePositivity.HomotopyFunctionComplex.OrdinaryBarSourceWordEmbedding
