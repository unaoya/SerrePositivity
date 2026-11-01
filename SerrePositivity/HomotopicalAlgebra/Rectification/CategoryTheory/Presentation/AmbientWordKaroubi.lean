module

public import SerrePositivity.HomotopicalAlgebra.Rectification.CategoryTheory.Presentation.AmbientWords
public import SerrePositivity.HomotopicalAlgebra.Rectification.CategoryTheory.Presentation.RetractWordRealization
public import SerrePositivity.HomotopicalAlgebra.Rectification.CategoryTheory.Presentation.RetractWordIdentities
public import Mathlib.CategoryTheory.Idempotents.Karoubi

/-!
# 中断した任意モデル源への一般化：AmbientWordKaroubi

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Decode formal retract vertices as actual idempotents of the ambient word presentation。

## 方針（定義・証明）
自由単体的分解・Dwyer–Kan型の生成射による整合化に対応する技法。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0021][inventory]を参照する。

[inventory]: ../../../../../formalization-plans/k-theory-generalization-inventory.md#m0021
[plan]: ../../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Decode formal retract vertices as actual idempotents of the ambient word presentation
-/

@[expose] public section
universe u v w
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Idempotents

namespace SerrePositivity.AmbientWords
variable (C : Type u) [Category.{v} C] (M : Type w) [MonoidWithZero M]

abbrev loop (X : C) (t : M) : (sourceFunctor C M).obj X ⟶ (sourceFunctor C M).obj X :=
  (quotient C M).map (word C M X t)

lemma loop_zero_idem (X : C) : loop C M X 0 ≫ loop C M X 0 = loop C M X 0 := by
  rw [← word_mul, zero_mul]

lemma loop_zero_left (X : C) (t : M) : loop C M X 0 ≫ loop C M X t = loop C M X 0 := by
  rw [← word_mul, zero_mul]

lemma loop_zero_right (X : C) (t : M) : loop C M X t ≫ loop C M X 0 = loop C M X 0 := by
  rw [← word_mul, mul_zero]

def toRetractRealization : Realization C M (RetractWords.Obj C M) where
  ambient := RetractWords.sourceFunctor C M
  action X t := (RetractWords.quotient C M).map (RetractWords.word C M X t)
  action_one := RetractWords.quotient_word_one C M
  action_mul X t z := by
    simpa using (CategoryTheory.Quotient.sound (RetractWords.Rel C M)
      (RetractWords.Rel.word_mul X t z)).symm

def toRetract : Obj C M ⥤ RetractWords.Obj C M := (toRetractRealization C M).functor

lemma toRetract_source {X Y : C} (f : X ⟶ Y) :
    (toRetract C M).map ((quotient C M).map (source C M f)) =
      (RetractWords.quotient C M).map (RetractWords.source C M f) :=
  (toRetractRealization C M).functor_source f

lemma toRetract_loop (X : C) (t : M) :
    (toRetract C M).map (loop C M X t) =
      (RetractWords.quotient C M).map (RetractWords.word C M X t) :=
  (toRetractRealization C M).functor_word X t

def smallObject (X : C) : Karoubi (Obj C M) :=
  ⟨(sourceFunctor C M).obj X, loop C M X 0, loop_zero_idem C M X⟩

def decodeRealization : RetractWords.Realization C M (Karoubi (Obj C M)) where
  ambient := sourceFunctor C M ⋙ toKaroubi (Obj C M)
  small := smallObject C M
  section_ X := ⟨loop C M X 0, by
    change loop C M X 0 ≫ loop C M X 0 ≫ 𝟙 _ = loop C M X 0
    rw [Category.comp_id, loop_zero_idem]⟩
  projection X := ⟨loop C M X 0, by
    change 𝟙 _ ≫ loop C M X 0 ≫ loop C M X 0 = loop C M X 0
    rw [Category.id_comp, loop_zero_idem]⟩
  action X t := ⟨loop C M X t, by simp⟩
  action_one X := by
    apply Karoubi.hom_ext
    exact word_one C M X
  action_mul X t z := by
    apply Karoubi.hom_ext
    exact word_mul C M X t z
  split X := by
    apply Karoubi.hom_ext
    exact loop_zero_idem C M X
  action_zero X := by
    apply Karoubi.hom_ext
    exact (loop_zero_idem C M X).symm
  section_action X t := by
    apply Karoubi.hom_ext
    exact loop_zero_left C M X t
  action_projection X t := by
    apply Karoubi.hom_ext
    exact loop_zero_right C M X t

def decode : RetractWords.Obj C M ⥤ Karoubi (Obj C M) := (decodeRealization C M).functor

end SerrePositivity.AmbientWords
