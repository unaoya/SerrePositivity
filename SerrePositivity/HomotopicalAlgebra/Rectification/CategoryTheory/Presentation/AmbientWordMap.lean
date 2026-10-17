module

public import SerrePositivity.HomotopicalAlgebra.Rectification.CategoryTheory.Presentation.AmbientWordComparison
public import SerrePositivity.HomotopicalAlgebra.Rectification.CategoryTheory.Presentation.RetractWordMap

/-!
# 中断した任意モデル源への一般化：AmbientWordMap

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：The ambient comparison commutes with source and word parameter maps。

## 方針（定義・証明）
自由単体的分解・Dwyer–Kan型の生成射による整合化に対応する技法。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0022][inventory]を参照する。

[inventory]: ../../../../../formalization-plans/k-theory-generalization-inventory.md#m0022
[plan]: ../../../../../formalization-plans/k-theory.md
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# The ambient comparison commutes with source and word parameter maps
-/

@[expose] public section
universe u v w u' v' w'
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory

namespace SerrePositivity.AmbientWords
variable {C : Type u} [Category.{v} C] {M : Type w} [MonoidWithZero M]
  {D : Type u'} [Category.{v'} D] {N : Type w'} [MonoidWithZero N]

def mapRealization (F : C ⥤ D) (h : M →*₀ N) : Realization C M (Obj D N) where
  ambient := F ⋙ sourceFunctor D N
  action X t := loop D N (F.obj X) (h t)
  action_one X := by
    change loop D N (F.obj X) (h 1) = 𝟙 _
    rw [map_one]
    exact word_one D N (F.obj X)
  action_mul X t z := by
    change loop D N (F.obj X) (h (t * z)) = _
    rw [map_mul]
    exact word_mul D N (F.obj X) (h t) (h z)

def map (F : C ⥤ D) (h : M →*₀ N) : Obj C M ⥤ Obj D N := (mapRealization F h).functor

lemma map_source (F : C ⥤ D) (h : M →*₀ N) {X Y : C} (f : X ⟶ Y) :
    (map F h).map ((quotient C M).map (source C M f)) =
      (quotient D N).map (source D N (F.map f)) :=
  (mapRealization F h).functor_source f

lemma map_loop (F : C ⥤ D) (h : M →*₀ N) (X : C) (t : M) :
    (map F h).map (loop C M X t) = loop D N (F.obj X) (h t) :=
  (mapRealization F h).functor_word X t

lemma map_toRetract (F : C ⥤ D) (h : M →*₀ N) :
    map F h ⋙ toRetract D N = toRetract C M ⋙ RetractWords.map F h := by
  apply functor_ext_generators
  · rintro ⟨X⟩
    cases X
    rfl
  · intro X Y e
    change Edge C M X Y at e
    cases e with
    | source f =>
      simp only [Functor.comp_map, map_source, toRetract_source, RetractWords.map_source]
      rfl
    | word X t =>
      simp only [Functor.comp_map, map_loop, toRetract_loop, RetractWords.map_word]
      rfl

end SerrePositivity.AmbientWords
