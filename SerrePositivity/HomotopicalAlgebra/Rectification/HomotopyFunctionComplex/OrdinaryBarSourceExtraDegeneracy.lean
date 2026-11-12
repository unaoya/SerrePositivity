module

public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarSourceExtraOperators
public import SerrePositivity.HomotopicalAlgebra.Simplicial.ExtraDegeneracyContraction

/-!
# 中断した任意モデル源への一般化：OrdinaryBarSourceExtraDegeneracy

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Singleton extra degeneracies on the actual forward source Hom augmentation。

## 方針（定義・証明）
frameによる導来写像空間と整合図式の厳密化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0225][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0225
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Singleton extra degeneracies on the actual forward source Hom augmentation
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory
open SerrePositivity.SimplicialModel

namespace SerrePositivity.HomotopyFunctionComplex.OrdinaryBarSourceExtraDegeneracy
open OrdinaryBarFreeResolutionSeed OrdinaryBarSourceExtraOperators
open FreeGeneratorDegeneracies
variable (C : Type u) [Category.{v} C] (X Y : D C)

def augmented : SimplicialObject.Augmented (Type (max u v)) where
  left := SimplexCategory.rev.op ⋙ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v} (OrdinaryBarSourceHom.hom C X Y)
  right := ULift.{max u v} (X ⟶ Y)
  hom := Functor.whiskerLeft SimplexCategory.rev.op (OrdinaryBarSourceHom.augmentation C X Y)

def extraDegeneracy : SimplicialObject.Augmented.ExtraDegeneracy (augmented C X Y) where
  s' := ↾fun f => ULift.up (singleton 0 (ULift.up f.down))
  s n := ↾fun f => ULift.up (singleton (n + 1) f.down)
  s'_comp_ε := by
    apply ConcreteCategory.hom_ext
    intro f
    apply ULift.ext
    change (OrdinaryBarFixedAugmentation.sourceProjection C
      (Opposite.op (SimplexCategory.mk 0))).map (singleton 0 (ULift.up f.down)) = f.down
    rw [projection_zero_map, face_zero_singleton]
  s₀_comp_δ₁ := by
    apply ConcreteCategory.hom_ext
    intro f
    apply ULift.ext
    change (OrdinaryBarSourceOperators.forwardHom C X Y).δ (1 : Fin 2)
      (singleton 1 f.down) = singleton 0 (ULift.up
        ((OrdinaryBarFixedAugmentation.sourceProjection C
          (Opposite.op (SimplexCategory.mk 0))).map f.down))
    rw [forward_hom_face, projection_zero_map]
    exact face_succ_singleton C 0 (0 : Fin 1) f.down

  s_comp_δ₀ n := by
    apply ConcreteCategory.hom_ext
    intro f
    apply ULift.ext
    change (OrdinaryBarSourceOperators.forwardHom C X Y).δ (0 : Fin (n + 2))
      (singleton (n + 1) f.down) = f.down
    rw [forward_hom_face, face_zero_singleton]

  s_comp_δ n i := by
    apply ConcreteCategory.hom_ext
    intro f
    apply ULift.ext
    change (OrdinaryBarFixedSource.literalMap C
        (SimplexCategory.rev.map (SimplexCategory.δ i.succ)).op).map (X := X) (Y := Y)
          (singleton (n + 2) f.down) = singleton (n + 1)
            ((OrdinaryBarFixedSource.literalMap C
              (SimplexCategory.rev.map (SimplexCategory.δ i)).op).map (X := X) (Y := Y) f.down)
    rw [forward_face_map, forward_face_map, face_succ_singleton]
  s_comp_σ n i := by
    apply ConcreteCategory.hom_ext
    intro f
    apply ULift.ext
    change (OrdinaryBarFixedSource.literalMap C
        (SimplexCategory.rev.map (SimplexCategory.σ i.succ)).op).map (X := X) (Y := Y)
          (singleton (n + 1) f.down) = singleton (n + 2)
            ((OrdinaryBarFixedSource.literalMap C
              (SimplexCategory.rev.map (SimplexCategory.σ i)).op).map (X := X) (Y := Y) f.down)
    rw [forward_degeneracy_map, forward_degeneracy_map, degeneracy_succ_singleton]

lemma localized_augmentation_isIso : IsIso (AnodyneHomotopy.anodyneQ.map
    (augmented C X Y).hom) :=
  ExtraDegeneracyContraction.localized_augmentation_isIso (extraDegeneracy C X Y)

end SerrePositivity.HomotopyFunctionComplex.OrdinaryBarSourceExtraDegeneracy
