module

public import Mathlib.Algebra.FreeMonoid.Basic
public import Mathlib.Algebra.GroupWithZero.WithZero

/-!
# 中断した任意モデル源への一般化：SegmentWords

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Finite words with a unit endpoint and an absorbing endpoint。

## 方針（定義・証明）
自由単体的分解・Dwyer–Kan型の生成射による整合化に対応する技法。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0551][inventory]を参照する。

[inventory]: ../../../formalization-plans/k-theory-generalization-inventory.md#m0551
[plan]: ../../../formalization-plans/k-theory.md
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Finite words with a unit endpoint and an absorbing endpoint

The normal form is a word of interior letters, or an absorbing zero.
Endpoint-preserving maps may send interior letters to either endpoint;
the universal property proves functoriality even in that case.
-/

@[expose] public section
universe u v w m
noncomputable section

namespace SerrePositivity.SimplicialModel.SegmentWords

abbrev Interior (A : Type u) (e z : A) := {a : A // a ≠ e ∧ a ≠ z}
abbrev Word (A : Type u) (e z : A) := WithZero (FreeMonoid (Interior A e z))

variable {A : Type u} {B : Type v} {D : Type w} (e z : A)

def letter (a : A) : Word A e z := by
  classical
  exact if he : a = e then 1 else if hz : a = z then 0 else
    (FreeMonoid.of (⟨a, he, hz⟩ : Interior A e z) : Word A e z)

lemma letter_unit : letter e z e = 1 := by classical simp [letter]

lemma letter_zero (hez : e ≠ z) : letter e z z = 0 := by
  classical
  simp [letter, Ne.symm hez]

lemma letter_interior (a : Interior A e z) :
    letter e z a.val = (FreeMonoid.of a : Word A e z) := by
  classical
  simp [letter, a.property.1, a.property.2]

/-- Evaluation into any monoid with an absorbing zero. -/
def lift {M : Type m} [MonoidWithZero M] (f : A → M) : Word A e z →*₀ M :=
  WithZero.lift' (FreeMonoid.lift (fun a : Interior A e z => f a.val))

lemma lift_letter {M : Type m} [MonoidWithZero M] (f : A → M) (he : f e = 1) (hz : f z = 0)
    (a : A) : lift e z f (letter e z a) = f a := by
  classical
  unfold letter
  split_ifs with ha hb
  · subst a; exact (map_one _).trans he.symm
  · subst a; exact (map_zero _).trans hz.symm
  · rfl

lemma hom_ext {M : Type m} [MonoidWithZero M] (f g : Word A e z →*₀ M)
    (h : ∀ a, f (letter e z a) = g (letter e z a)) : f = g := by
  apply WithZero.monoidWithZeroHom_ext
  apply FreeMonoid.hom_eq
  intro a
  change f (FreeMonoid.of a : Word A e z) = g (FreeMonoid.of a : Word A e z)
  simpa only [letter_interior] using h a.val

variable {e z} {eB zB : B} {eD zD : D}

def map (f : A → B) : Word A e z →*₀ Word B eB zB := lift e z (fun a => letter eB zB (f a))

lemma map_letter (hzB : eB ≠ zB) (f : A → B) (he : f e = eB) (hz : f z = zB) (a : A) :
    map f (letter e z a) = letter eB zB (f a) :=
  lift_letter e z _ (he ▸ letter_unit eB zB) (hz ▸ letter_zero eB zB hzB) a

lemma map_id (hez : e ≠ z) : (map id : Word A e z →*₀ Word A e z) = MonoidWithZeroHom.id _ := by
  apply hom_ext e z
  intro a
  rw [map_letter hez id rfl rfl]
  rfl

lemma map_comp (hzB : eB ≠ zB) (hzD : eD ≠ zD)
    (f : A → B) (g : B → D) (he : f e = eB) (hz : f z = zB)
    (he' : g eB = eD) (hz' : g zB = zD) :
    (map (g ∘ f) : Word A e z →*₀ Word D eD zD) =
      (map (e := eB) (z := zB) (eB := eD) (zB := zD) g).comp
        (map (eB := eB) (zB := zB) f) := by
  apply hom_ext e z
  intro a
  rw [map_letter hzD (g ∘ f) (by simp [he, he']) (by simp [hz, hz']),
    MonoidWithZeroHom.comp_apply, map_letter hzB f he hz, map_letter hzD g he' hz']
  rfl

end SerrePositivity.SimplicialModel.SegmentWords
