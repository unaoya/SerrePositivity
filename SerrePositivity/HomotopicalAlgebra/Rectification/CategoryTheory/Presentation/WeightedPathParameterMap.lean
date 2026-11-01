module

public import SerrePositivity.HomotopicalAlgebra.Rectification.CategoryTheory.Presentation.WeightedPathRealization
public import SerrePositivity.HomotopicalAlgebra.Rectification.CategoryTheory.Presentation.AmbientWordMap
public import SerrePositivity.HomotopicalAlgebra.Rectification.CategoryTheory.Presentation.AmbientWordAugmentation

/-!
# 中断した任意モデル源への一般化：WeightedPathParameterMap

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Normal forms preserve the actual word-parameter maps and augmentation。

## 方針（定義・証明）
自由単体的分解・Dwyer–Kan型の生成射による整合化に対応する技法。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0031][inventory]を参照する。

[inventory]: ../../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0031
[plan]: ../../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Normal forms preserve the actual word-parameter maps and augmentation
-/

@[expose] public section
universe u v w w'
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory

namespace SerrePositivity.QuiverWeightedPaths
variable (V : Type u) [Quiver.{v} V]

section Augmentation
variable (M : Type w) [Monoid M]

lemma augmentation_eval {X Y : V} (p : Path V M X Y) :
    (AmbientWords.augmentation (Paths V) M).map (eval V M p) = forget p := by
  induction p with
  | nil t => exact AmbientWords.augmentation_word (Paths V) M X t
  | @cons Y Z p e t ih =>
    change (AmbientWords.augmentation (Paths V) M).map
      (eval V M p ≫ (targetSource V M).map e.toPath ≫ wordAt V M _ t) = _
    rw [Functor.map_comp, Functor.map_comp, ih]
    have hs : (AmbientWords.augmentation (Paths V) M).map
        ((targetSource V M).map e.toPath) = e.toPath :=
      AmbientWords.augmentation_source (Paths V) M e.toPath
    rw [hs]
    have ht : (AmbientWords.augmentation (Paths V) M).map (wordAt V M Z t) =
        𝟙 (show Paths V from Z) :=
      AmbientWords.augmentation_word (Paths V) M Z t
    rw [ht]
    rfl

end Augmentation

variable {M : Type w} [MonoidWithZero M] {N : Type w'} [MonoidWithZero N]

lemma parameter_word (h : M →*₀ N) (X : V) (t : M) :
    (AmbientWords.map (𝟭 (Paths V)) h).map (wordAt V M X t) = wordAt V N X (h t) :=
  AmbientWords.map_loop (𝟭 (Paths V)) h X t

lemma parameter_source (h : M →*₀ N) {X Y : V} (p : Quiver.Path X Y) :
    (AmbientWords.map (𝟭 (Paths V)) h).map ((targetSource V M).map p) =
      (targetSource V N).map p := AmbientWords.map_source (𝟭 (Paths V)) h p

lemma map_eval (h : M →*₀ N) {X Y : V} (p : Path V M X Y) :
    (AmbientWords.map (𝟭 (Paths V)) h).map (eval V M p) = eval V N (mapWeights h p) := by
  induction p with
  | nil t => exact parameter_word V h X t
  | cons p e t ih =>
    change (AmbientWords.map (𝟭 (Paths V)) h).map
      (eval V M p ≫ (targetSource V M).map e.toPath ≫ wordAt V M _ t) = _
    rw [Functor.map_comp, Functor.map_comp, ih, parameter_source, parameter_word]
    rfl

end SerrePositivity.QuiverWeightedPaths
