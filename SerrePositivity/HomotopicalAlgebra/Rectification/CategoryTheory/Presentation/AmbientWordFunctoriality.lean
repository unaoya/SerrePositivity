module

public import SerrePositivity.HomotopicalAlgebra.Rectification.CategoryTheory.Presentation.RetractWordAugmentation
public import SerrePositivity.HomotopicalAlgebra.Rectification.CategoryTheory.Presentation.AmbientWordMap
public import SerrePositivity.HomotopicalAlgebra.Rectification.CategoryTheory.Presentation.AmbientWordAugmentation

/-!
# 中断した任意モデル源への一般化：AmbientWordFunctoriality

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Strict functoriality and naturality of the actual ambient-word augmentation。

## 方針（定義・証明）
自由単体的分解・Dwyer–Kan型の生成射による整合化に対応する技法。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0020][inventory]を参照する。

[inventory]: ../../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0020
[plan]: ../../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Strict functoriality and naturality of the actual ambient-word augmentation
-/

@[expose] public section
universe u v w u' v' w' u'' v'' w''
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory

namespace SerrePositivity.AmbientWords
variable {C : Type u} [Category.{v} C] {M : Type w} [MonoidWithZero M]
  {D : Type u'} [Category.{v'} D] {N : Type w'} [MonoidWithZero N]
  {E : Type u''} [Category.{v''} E] {O : Type w''} [MonoidWithZero O]

lemma map_id : map (𝟭 C) (MonoidWithZeroHom.id M) = 𝟭 (Obj C M) := by
  apply functor_ext_generators
  · rintro ⟨X⟩
    cases X
    rfl
  · intro X Y e
    change Edge C M X Y at e
    cases e with
    | source f => simp only [map_source]; rfl
    | word X t => simp only [map_loop]; rfl

lemma map_comp (F : C ⥤ D) (G : D ⥤ E) (h : M →*₀ N) (k : N →*₀ O) :
    map (F ⋙ G) (k.comp h) = map F h ⋙ map G k := by
  apply functor_ext_generators
  · rintro ⟨X⟩
    cases X
    rfl
  · intro X Y e
    change Edge C M X Y at e
    cases e with
    | source f => simp only [Functor.comp_map, map_source]; rfl
    | word X t => simp only [Functor.comp_map, map_loop]; rfl

lemma commute (F : C ⥤ D) (h : M →*₀ N) :
    map F (MonoidWithZeroHom.id M) ⋙ map (𝟭 D) h =
      map (𝟭 C) h ⋙ map F (MonoidWithZeroHom.id N) := by
  rw [← map_comp, ← map_comp]
  simp only [Functor.comp_id, Functor.id_comp, MonoidWithZeroHom.comp_id,
    MonoidWithZeroHom.id_comp]

lemma map_augmentation (F : C ⥤ D) (h : M →*₀ N) :
    map F h ⋙ augmentation D N = augmentation C M ⋙ F := by
  apply functor_ext_generators
  · rintro ⟨X⟩
    cases X
    rfl
  · intro X Y e
    change Edge C M X Y at e
    cases e with
    | source f =>
      simp only [Functor.comp_map, map_source]
      exact heq_of_eq ((augmentation_source D N (F.map f)).trans
        (congrArg (fun g => F.map g) (augmentation_source C M f)).symm)
    | word X t =>
      simp only [Functor.comp_map, map_loop, augmentation_word]
      exact heq_of_eq (F.map_id X).symm

lemma toRetract_augmentation :
    toRetract C M ⋙ RetractWords.augmentation C M = augmentation C M := by
  apply functor_ext_generators
  · rintro ⟨X⟩
    cases X
    rfl
  · intro X Y e
    change Edge C M X Y at e
    cases e with
    | source f =>
      simp only [Functor.comp_map, toRetract_source, RetractWords.augmentation_source]
      exact heq_of_eq (augmentation_source C M f).symm
    | word X t =>
      simp only [Functor.comp_map, toRetract_loop, RetractWords.augmentation_word,
        augmentation_word]
      rfl

end SerrePositivity.AmbientWords
