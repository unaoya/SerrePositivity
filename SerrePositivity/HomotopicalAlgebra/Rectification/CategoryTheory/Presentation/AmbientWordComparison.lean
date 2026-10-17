module

public import SerrePositivity.HomotopicalAlgebra.Rectification.CategoryTheory.Presentation.AmbientWordKaroubi
public import SerrePositivity.CategoryTheory.Quiver.PathNatTrans
public import Mathlib.CategoryTheory.Idempotents.FunctorExtension

/-!
# 中断した任意モデル源への一般化：AmbientWordComparison

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：The ambient word embedding has an explicit inverse on ambient Hom sets。

## 方針（定義・証明）
自由単体的分解・Dwyer–Kan型の生成射による整合化に対応する技法。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0019][inventory]を参照する。

[inventory]: ../../../../../formalization-plans/k-theory-generalization-inventory.md#m0019
[plan]: ../../../../../formalization-plans/k-theory.md
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# The ambient word embedding has an explicit inverse on ambient Hom sets
-/

@[expose] public section
universe u v w
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Idempotents

namespace SerrePositivity.AmbientWords
variable (C : Type u) [Category.{v} C] (M : Type w) [MonoidWithZero M]

lemma toRetract_decode : toRetract C M ⋙ decode C M = toKaroubi (Obj C M) := by
  apply functor_ext_generators
  · rintro ⟨X⟩
    cases X
    rfl
  · intro X Y e
    change Edge C M X Y at e
    cases e with
    | source f =>
      simp only [Functor.comp_map, toRetract_source, decode,
        RetractWords.Realization.functor_source]
      rfl
    | word X t =>
      simp only [Functor.comp_map, toRetract_loop, decode,
        RetractWords.Realization.functor_word]
      rfl

abbrev decodeHom {X Y : C}
    (f : (RetractWords.sourceFunctor C M).obj X ⟶ (RetractWords.sourceFunctor C M).obj Y) :
    (sourceFunctor C M).obj X ⟶ (sourceFunctor C M).obj Y :=
  ((decode C M).map f).f

lemma decodeHom_toRetract {X Y : C}
    (f : (sourceFunctor C M).obj X ⟶ (sourceFunctor C M).obj Y) :
    decodeHom C M ((toRetract C M).map f) = f := by
  have h := congr($(toRetract_decode C M).map f)
  exact congrArg Karoubi.Hom.f h

abbrev decodeEmbedded : RetractWords.Obj C M ⥤ Karoubi (RetractWords.Obj C M) :=
  decode C M ⋙ (functorExtension₂ (Obj C M) (RetractWords.Obj C M)).obj (toRetract C M)

def comparisonApp (X : RetractWords.Vertex C M) :
    (decodeEmbedded C M).obj ((RetractWords.quotient C M).obj X) ⟶
      (toKaroubi (RetractWords.Obj C M)).obj ((RetractWords.quotient C M).obj X) := by
  cases X with
  | ambient X =>
    refine ⟨𝟙 _, ?_⟩
    change (toRetract C M).map (𝟙 _) ≫ 𝟙 _ ≫ 𝟙 _ = 𝟙 _
    rw [(toRetract C M).map_id, Category.comp_id, Category.id_comp]
  | small X =>
    refine ⟨(RetractWords.quotient C M).map (RetractWords.projection C M X), ?_⟩
    change (toRetract C M).map (loop C M X 0) ≫ _ ≫ 𝟙 _ = _
    rw [toRetract_loop, RetractWords.quotient_word_zero, Category.comp_id]
    simp only [Category.assoc, RetractWords.quotient_split, Category.comp_id]

def comparison : decodeEmbedded C M ⟶ toKaroubi (RetractWords.Obj C M) :=
  CategoryTheory.Quotient.natTransLift (RetractWords.Rel C M)
    (QuiverPaths.natTransOfEdges _ _ (comparisonApp C M) (by
      intro X Y e
      change RetractWords.Edge C M X Y at e
      apply Karoubi.hom_ext
      cases e with
      | source f =>
        change (toRetract C M).map ((sourceFunctor C M).map f) ≫ 𝟙 _ =
          𝟙 _ ≫ (RetractWords.sourceFunctor C M).map f
        rw [Category.comp_id, Category.id_comp]
        exact toRetract_source C M f
      | word X t =>
        change (toRetract C M).map (loop C M X t) ≫ 𝟙 _ =
          𝟙 _ ≫ (RetractWords.quotient C M).map (RetractWords.word C M X t)
        rw [toRetract_loop, Category.comp_id, Category.id_comp]
      | section_ X =>
        simp only [Functor.comp_map, Karoubi.comp_f, decodeEmbedded, decode,
          RetractWords.Realization.functor_section]
        change (toRetract C M).map (loop C M X 0) ≫ 𝟙 _ =
          (RetractWords.quotient C M).map (RetractWords.projection C M X) ≫
            (RetractWords.quotient C M).map (RetractWords.section_ C M X)
        rw [toRetract_loop, Category.comp_id, RetractWords.quotient_word_zero]
      | projection X =>
        change (toRetract C M).map (loop C M X 0) ≫
          (RetractWords.quotient C M).map (RetractWords.projection C M X) =
            𝟙 _ ≫ (RetractWords.quotient C M).map (RetractWords.projection C M X)
        rw [toRetract_loop, RetractWords.quotient_word_zero, Category.id_comp]
        simp only [Category.assoc, RetractWords.quotient_split, Category.comp_id]))

lemma toRetract_decodeHom {X Y : C}
    (f : (RetractWords.sourceFunctor C M).obj X ⟶ (RetractWords.sourceFunctor C M).obj Y) :
    (toRetract C M).map (decodeHom C M f) = f := by
  have h := congrArg Karoubi.Hom.f ((comparison C M).naturality f)
  change (toRetract C M).map (decodeHom C M f) ≫ 𝟙 _ = 𝟙 _ ≫ f at h
  simpa only [Category.comp_id, Category.id_comp] using h

def ambientHomEquiv (X Y : C) :
    ((sourceFunctor C M).obj X ⟶ (sourceFunctor C M).obj Y) ≃
      ((RetractWords.sourceFunctor C M).obj X ⟶ (RetractWords.sourceFunctor C M).obj Y) where
  toFun := (toRetract C M).map
  invFun := decodeHom C M
  left_inv := decodeHom_toRetract C M
  right_inv := toRetract_decodeHom C M

end SerrePositivity.AmbientWords
