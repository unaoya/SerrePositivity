module

public import SerrePositivity.HomotopicalAlgebra.Rectification.CategoryTheory.Presentation.RetractWordExt
public import SerrePositivity.HomotopicalAlgebra.Rectification.CategoryTheory.Presentation.RetractWordMap

/-!
# 中断した任意モデル源への一般化：RetractWordAugmentation

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Naturality of the actual augmentation in source and word parameters。

## 方針（定義・証明）
自由単体的分解・Dwyer–Kan型の生成射による整合化に対応する技法。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0024][inventory]を参照する。

[inventory]: ../../../../../formalization-plans/k-theory-generalization-inventory.md#m0024
[plan]: ../../../../../formalization-plans/k-theory.md
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Naturality of the actual augmentation in source and word parameters
-/

@[expose] public section
universe u v w u' v' w'
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory

namespace SerrePositivity.RetractWords
variable {C : Type u} [Category.{v} C] {M : Type w} [MonoidWithZero M]

lemma augmentation_source {X Y : C} (f : X ⟶ Y) :
    (augmentation C M).map ((quotient C M).map (source C M f)) = f :=
  Paths.lift_toPath (augmentationEdges C M) (Edge.source f)

lemma augmentation_word (X : C) (t : M) :
    (augmentation C M).map ((quotient C M).map (word C M X t)) = 𝟙 X :=
  Paths.lift_toPath (augmentationEdges C M) (Edge.word X t)

lemma augmentation_section (X : C) :
    (augmentation C M).map ((quotient C M).map (section_ C M X)) = 𝟙 X :=
  Paths.lift_toPath (augmentationEdges C M) (Edge.section_ X)

lemma augmentation_projection (X : C) :
    (augmentation C M).map ((quotient C M).map (projection C M X)) = 𝟙 X :=
  Paths.lift_toPath (augmentationEdges C M) (Edge.projection X)

variable {D : Type u'} [Category.{v'} D] {N : Type w'} [MonoidWithZero N]
lemma map_augmentation (F : C ⥤ D) (h : M →*₀ N) :
    map F h ⋙ augmentation D N = augmentation C M ⋙ F := by
  apply functor_ext_generators (C := C) (M := M)
  · rintro ⟨X⟩
    cases X <;> rfl
  · intro X Y e
    change Edge C M X Y at e
    cases e with
    | source f =>
      simp only [Functor.comp_map, map_source, augmentation_source]
      rfl
    | word X t =>
      simp only [Functor.comp_map, map_word, augmentation_word]
      exact heq_of_eq (F.map_id X).symm
    | section_ X =>
      simp only [Functor.comp_map, map_section, augmentation_section]
      exact heq_of_eq (F.map_id X).symm
    | projection X =>
      simp only [Functor.comp_map, map_projection, augmentation_projection]
      exact heq_of_eq (F.map_id X).symm

lemma source_map (F : C ⥤ D) (h : M →*₀ N) :
    sourceFunctor C M ⋙ map F h = F ⋙ sourceFunctor D N := by
  refine CategoryTheory.Functor.ext (F := sourceFunctor C M ⋙ map F h)
    (G := F ⋙ sourceFunctor D N) (fun _ => rfl) ?_
  intro X Y f
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  change (map F h).map ((quotient C M).map (source C M f)) =
    (quotient D N).map (source D N (F.map f))
  exact map_source F h f

end SerrePositivity.RetractWords
