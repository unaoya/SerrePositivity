module

public import SerrePositivity.HomotopicalAlgebra.Rectification.CategoryTheory.Quiver.WeightedPaths

/-!
# 中断した任意モデル源への一般化：WeightedPathMaps

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Arbitrary weight substitutions and the underlying unweighted path。

## 方針（定義・証明）
自由単体的分解・Dwyer–Kan型の生成射による整合化に対応する技法。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0037][inventory]を参照する。

[inventory]: ../../../../../formalization-plans/k-theory-generalization-inventory.md#m0037
[plan]: ../../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Arbitrary weight substitutions and the underlying unweighted path
-/

@[expose] public section
universe u v w w' w''
open CategoryTheory

namespace SerrePositivity.QuiverWeightedPaths
variable {V : Type u} [Quiver.{v} V] {M : Type w} {N : Type w'} {O : Type w''}

def mapWeights (f : M → N) {X Y : V} : Path V M X Y → Path V N X Y
  | .nil t => .nil (f t)
  | .cons p e t => .cons (mapWeights f p) e (f t)

lemma mapWeights_id {X Y : V} (p : Path V M X Y) : mapWeights id p = p := by
  induction p with
  | nil t => rfl
  | cons p e t ih => simp only [mapWeights, ih, id_eq]

lemma mapWeights_comp (f : M → N) (g : N → O) {X Y : V} (p : Path V M X Y) :
    mapWeights g (mapWeights f p) = mapWeights (g ∘ f) p := by
  induction p with
  | nil t => rfl
  | cons p e t ih => simp only [mapWeights, ih, Function.comp_apply]

def forget {X Y : V} : Path V M X Y → Quiver.Path X Y
  | .nil _ => .nil
  | .cons p e _ => .cons (forget p) e

def fill (t : M) {X Y : V} : Quiver.Path X Y → Path V M X Y
  | .nil => .nil t
  | .cons p e => .cons (fill t p) e t

lemma forget_mapWeights (f : M → N) {X Y : V} (p : Path V M X Y) :
    forget (mapWeights f p) = forget p := by
  induction p with
  | nil t => rfl
  | cons p e t ih => simp only [forget, mapWeights, ih]

lemma forget_fill (t : M) {X Y : V} (p : Quiver.Path X Y) : forget (fill t p) = p := by
  induction p with
  | nil => rfl
  | cons p e ih => simp only [forget, fill, ih]

lemma mapWeights_fill (f : M → N) (t : M) {X Y : V} (p : Quiver.Path X Y) :
    mapWeights f (fill t p) = fill (f t) p := by
  induction p with
  | nil => rfl
  | cons p e ih => simp only [mapWeights, fill, ih]

lemma mapWeights_const (t : N) {X Y : V} (p : Path V M X Y) :
    mapWeights (fun _ => t) p = fill t (forget p) := by
  induction p with
  | nil a => rfl
  | cons p e a ih => simp only [mapWeights, fill, forget, ih]

end SerrePositivity.QuiverWeightedPaths
