module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FreePathResolutionDegreeTwo

/-!
# 自由な道の分解の次数二の二つの退化生成元像の交わりを計算する

## 概要
自由な道の分解の次数二の二つの退化生成元像の交わりを計算する。
一般に再利用できる道具として分類Aに整理する。

## 方針（定義・証明）
余単位と余乗法、または自由な道の生成射を各次数で明示する。
面・退化の関係式と生成射上の一致から、全体の自然性と比較を導く。

## 規約と注意
宇宙・境界・比較射は各宣言に指定されたものを用いる。
対象ごとの選択から自然性や厳密な合成則を暗黙には推論しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない（依存監査で確認済み）。
今後はWaldhausenのS-構成の二重単体図式や分解の比較・加法性の準備に利用できる。
[棚卸し m0097][inventory]と[計画書 §396][plan]を参照。

[inventory]: ../../../formalization-plans/k-theory-generalization-inventory.md#m0097
[plan]: ../../../formalization-plans/k-theory.md
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# The exact intersection of the two degree-two degeneracy generator images

A path duplicated from the original category can be a singleton only if
both its preimage and its inner singleton are the same original generator.
The counit gives strict, actual recovery of all preimages.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory

namespace SerrePositivity.HomotopyFunctionComplex.FreePathDegeneracyImage
open FreePathResolution
variable {C : Type u} [Category.{v} C]

lemma toPath_injective {V : Type*} [Quiver V] {X Y : V} :
    Function.Injective (fun f : X ⟶ Y => f.toPath) := by
  intro f g h
  cases h
  rfl

lemma duplicate_length {X Y : C} (p : Quiver.Path X Y) :
    ((duplicate C).map p).length = p.length := by
  induction p with
  | nil => rfl
  | cons p f ih =>
    change ((duplicate C).map p).length + 1 = p.length + 1
    exact congrArg Nat.succ ih

lemma singleton_of_length_one {V : Type*} [Quiver V] {X Y : V} (p : Quiver.Path X Y)
    (h : p.length = 1) : ∃ f : X ⟶ Y, p = f.toPath := by
  cases p with
  | nil => simp at h
  | @cons Z Y p f =>
    have hp : p.length = 0 := by simpa only [Quiver.Path.length_cons, Nat.add_eq_right] using h
    obtain rfl := Quiver.Path.eq_of_length_zero p hp
    obtain rfl := Quiver.Path.eq_nil_of_length_zero p hp
    exact ⟨f, rfl⟩

lemma duplicate_eq_singleton {X Y : C} (p q : Quiver.Path X Y)
    (h : (duplicate C).map p = Quiver.Hom.toPath (V := Paths C) q) :
    ∃ f : X ⟶ Y, p = f.toPath ∧ q = f.toPath := by
  have hp : p.length = 1 := by
    have hl := congrArg Quiver.Path.length h
    simpa only [duplicate_length, Quiver.Path.length_toPath] using hl
  obtain ⟨f, rfl⟩ := singleton_of_length_one p hp
  rw [duplicate_generator] at h
  exact ⟨f, rfl, (toPath_injective h).symm⟩

lemma duplicate_map_injective {X Y : C} : Function.Injective
    (fun p : Quiver.Path X Y => (duplicate C).map p) := by
  intro p q h
  have hh := congrArg (counit (Paths C)).map h
  have hp := congr($(left_counit (C := C)).map p)
  have hq := congr($(left_counit (C := C)).map q)
  exact hp.symm.trans (hh.trans hq)

lemma counit_duplicate {X Y : C} (p : Quiver.Path X Y) :
    (counit (Paths C)).map ((duplicate C).map p) = p :=
  congr($(left_counit (C := C)).map p)

/- 旧宣言の技術注記：Both types of degenerate generators have a common image exactly at double singletons. -/
/-- 自由な道の分解の次数二の二つの退化生成元像の交わりを計算する。

宇宙・境界・比較射は各宣言に指定されたものを用いる。
余単位と余乗法、または自由な道の生成射を各次数で明示する。
面・退化の関係式と生成射上の一致から、全体の自然性と比較を導く。
-/

lemma generator_image_intersection {X Y : C} (p q : Quiver.Path X Y) :
    Quiver.Hom.toPath (V := Paths C) q = (duplicate C).map p ↔
      ∃ f : X ⟶ Y, p = f.toPath ∧ q = f.toPath := by
  constructor
  · intro h
    exact duplicate_eq_singleton p q h.symm
  · rintro ⟨f, rfl, rfl⟩
    exact (duplicate_generator f).symm

end SerrePositivity.HomotopyFunctionComplex.FreePathDegeneracyImage
