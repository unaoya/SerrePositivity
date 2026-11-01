module

public import Mathlib.CategoryTheory.PathCategory.Basic
public import Mathlib.Algebra.Group.Defs

/-!
# 中断した任意モデル源への一般化：WeightedPaths

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Paths with independent monoid weights at every vertex。

## 方針（定義・証明）
自由単体的分解・Dwyer–Kan型の生成射による整合化に対応する技法。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0038][inventory]を参照する。

[inventory]: ../../../../../formalization-plans/k-theory-generalization-inventory.md#m0038
[plan]: ../../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Paths with independent monoid weights at every vertex
-/

@[expose] public section
universe u v w
open CategoryTheory

namespace SerrePositivity.QuiverWeightedPaths
variable (V : Type u) [Quiver.{v} V] (M : Type w)

inductive Path : V → V → Type (max u v w)
  | nil {X : V} (t : M) : Path X X
  | cons {X Y Z : V} (p : Path X Y) (e : Y ⟶ Z) (t : M) : Path X Z

variable {V M} [Monoid M]

def mulLast {X Y : V} : Path V M X Y → M → Path V M X Y
  | .nil a, t => .nil (a * t)
  | .cons p e a, t => .cons p e (a * t)

def comp {X Y Z : V} (p : Path V M X Y) : Path V M Y Z → Path V M X Z
  | .nil t => mulLast p t
  | .cons q e t => .cons (comp p q) e t

lemma mulLast_one {X Y : V} (p : Path V M X Y) : mulLast p 1 = p := by
  cases p <;> simp [mulLast]

lemma mulLast_mul {X Y : V} (p : Path V M X Y) (a b : M) :
    mulLast (mulLast p a) b = mulLast p (a * b) := by
  cases p <;> simp [mulLast, mul_assoc]

lemma mulLast_comp {X Y Z : V} (p : Path V M X Y) (q : Path V M Y Z) (t : M) :
    mulLast (comp p q) t = comp p (mulLast q t) := by
  cases q with
  | nil a => exact mulLast_mul p a t
  | cons q e a => rfl

lemma nil_comp {X Y : V} (p : Path V M X Y) : comp (.nil 1) p = p := by
  induction p with
  | nil t => simp [comp, mulLast]
  | cons p e t ih => simp only [comp, ih]

lemma comp_assoc {W X Y Z : V} (p : Path V M W X) (q : Path V M X Y) (r : Path V M Y Z) :
    comp (comp p q) r = comp p (comp q r) := by
  induction r with
  | nil t => exact mulLast_comp p q t
  | cons r e t ih => simp only [comp, ih]

def Obj (V : Type u) (_M : Type w) : Type u := V

instance : Category.{max u v w} (Obj V M) where
  Hom X Y := Path V M X Y
  id _ := .nil 1
  comp := comp
  id_comp := nil_comp
  comp_id := mulLast_one
  assoc := comp_assoc

def generators : V ⥤q Obj V M where
  obj X := X
  map e := .cons (.nil 1) e 1

def sourceFunctor : Paths V ⥤ Obj V M := Paths.lift (generators (V := V) (M := M))

end SerrePositivity.QuiverWeightedPaths
