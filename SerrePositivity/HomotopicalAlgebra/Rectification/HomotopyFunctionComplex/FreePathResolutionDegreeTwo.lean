module

public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.FreePathResolution

/-!
# 中断した任意モデル源への一般化：FreePathResolutionDegreeTwo

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Faces, degeneracies and overlaps in degree two of the actual free-path resolution。

## 方針（定義・証明）
自由単体的分解・Dwyer–Kan型の生成射による整合化に対応する技法。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0099][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0099
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Faces, degeneracies and overlaps in degree two of the actual free-path resolution

These functors use the original category directly, so they apply to the
existing choice-cover comparison without a change of source presentation.
No model structure is required.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory

namespace SerrePositivity.HomotopyFunctionComplex.FreePathResolutionDegreeTwo
open FreePathResolution
variable (C : Type u) [Category.{v} C]

abbrev lowerZero : Paths (Paths C) ⥤ Paths C := counit (Paths C)
abbrev lowerOne : Paths (Paths C) ⥤ Paths C := map (counit C)
abbrev faceZero : Paths (Paths (Paths C)) ⥤ Paths (Paths C) := counit (Paths (Paths C))
abbrev faceOne : Paths (Paths (Paths C)) ⥤ Paths (Paths C) := map (counit (Paths C))
abbrev faceTwo : Paths (Paths (Paths C)) ⥤ Paths (Paths C) := map (map (counit C))
abbrev degeneracyZero : Paths (Paths C) ⥤ Paths (Paths (Paths C)) := duplicate (Paths C)
abbrev degeneracyOne : Paths (Paths C) ⥤ Paths (Paths (Paths C)) := map (duplicate C)

lemma faceOne_lowerZero : faceOne C ⋙ lowerZero C = faceZero C ⋙ lowerZero C :=
  counit_naturality (counit (Paths C))

lemma faceTwo_lowerZero : faceTwo C ⋙ lowerZero C = faceZero C ⋙ lowerOne C :=
  counit_naturality (map (counit C))

lemma faceTwo_lowerOne : faceTwo C ⋙ lowerOne C = faceOne C ⋙ lowerOne C := by
  change map (map (counit C)) ⋙ map (counit C) =
    map (counit (Paths C)) ⋙ map (counit C)
  rw [← map_comp, ← map_comp, counit_naturality (counit C)]

lemma degeneracyZero_faceZero : degeneracyZero C ⋙ faceZero C = 𝟭 _ := left_counit
lemma degeneracyZero_faceOne : degeneracyZero C ⋙ faceOne C = 𝟭 _ := right_counit

lemma degeneracyZero_faceTwo :
    degeneracyZero C ⋙ faceTwo C = lowerOne C ⋙ duplicate C :=
  (duplicate_naturality (counit C)).symm

lemma degeneracyOne_faceZero :
    degeneracyOne C ⋙ faceZero C = lowerZero C ⋙ duplicate C :=
  counit_naturality (duplicate C)

lemma degeneracyOne_faceOne : degeneracyOne C ⋙ faceOne C = 𝟭 _ := by
  change map (duplicate C) ⋙ map (counit (Paths C)) = _
  rw [← map_comp, left_counit, map_id]

lemma degeneracyOne_faceTwo : degeneracyOne C ⋙ faceTwo C = 𝟭 _ := by
  change map (duplicate C) ⋙ map (map (counit C)) = _
  rw [← map_comp, right_counit, map_id]

lemma degeneracy_overlap : duplicate C ⋙ degeneracyZero C = duplicate C ⋙ degeneracyOne C :=
  coassociativity.symm

end SerrePositivity.HomotopyFunctionComplex.FreePathResolutionDegreeTwo
