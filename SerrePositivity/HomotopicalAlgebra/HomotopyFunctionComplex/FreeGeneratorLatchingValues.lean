module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FreeGeneratorDegeneracies
public import Lean.Elab.Tactic.Omega

/-!
# 全退化像の和への降下は各退化像上の指定値によって一意に決まる

## 概要
全退化像の和への降下は各退化像上の指定値によって一意に決まる。
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
[棚卸し m0095][inventory]と[計画書 §396][plan]を参照。

[inventory]: ../../../formalization-plans/k-theory-generalization-inventory.md#m0095
[plan]: ../../../formalization-plans/k-theory.md
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Compatible values on the union of all free-generator degeneracy images

The pairwise double-degeneracy equations suffice to descend prescribed values
onto the entire union. No disjointness of degeneracy images is assumed.
-/

@[expose] public section
universe v u w w'
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.HomotopyFunctionComplex.FreeGeneratorLatchingValues
open FreeGeneratorDegeneracies
variable {V : Type u} [Quiver.{v} V] {X Y : V} (n : ℕ) {T : Sort w}
  (value : Fin (n + 2) → hom (n + 1) X Y → T)

/-- Agreement on all double-degeneracy overlaps, in their ordered presentation. -/
def Compatible : Prop := ∀ (i j : Fin (n + 1)), i ≤ j → ∀ r : hom n X Y,
  value i.castSucc (degeneracy n j r) = value j.succ (degeneracy n i r)

lemma values_agree_ordered (h : Compatible n value) (i j : Fin (n + 2)) (hij : i < j)
    (p q : hom (n + 1) X Y)
    (hpq : degeneracy (n + 1) i p = degeneracy (n + 1) j q) : value i p = value j q := by
  let a : Fin (n + 1) := ⟨i.val, by omega⟩
  let b : Fin (n + 1) := ⟨j.val - 1, by omega⟩
  have ha : a.castSucc = i := Fin.ext rfl
  have hb : b.succ = j := Fin.ext (by dsimp [b]; omega)
  have hab : a ≤ b := by change i.val ≤ j.val - 1; omega
  rw [← ha, ← hb] at hpq ⊢
  obtain ⟨r, rfl, rfl⟩ := degeneracy_intersection n a b hab p q hpq
  exact h a b hab r

lemma values_agree (h : Compatible n value) (i j : Fin (n + 2))
    (p q : hom (n + 1) X Y)
    (hpq : degeneracy (n + 1) i p = degeneracy (n + 1) j q) : value i p = value j q := by
  rcases lt_trichotomy i j with hij | rfl | hji
  · exact values_agree_ordered n value h i j hij p q hpq
  · exact congrArg (value i) (degeneracy_injective (n + 1) i hpq)
  · exact (values_agree_ordered n value h j i hji q p hpq.symm).symm

/-- The entire union of the degeneracy images in the next generator degree. -/
def Fixed (e : hom (n + 2) X Y) : Prop :=
  ∃ i : Fin (n + 2), ∃ p : hom (n + 1) X Y, e = degeneracy (n + 1) i p

lemma fixed_degeneracy (i : Fin (n + 2)) (p : hom (n + 1) X Y) :
    Fixed n (degeneracy (n + 1) i p) := ⟨i, p, rfl⟩

/-- Pick any presentation; `desc_eq` proves independence from this choice. -/
def desc (e : hom (n + 2) X Y) (he : Fixed n e) : T :=
  value he.choose he.choose_spec.choose

lemma desc_eq (h : Compatible n value) (e : hom (n + 2) X Y) (he : Fixed n e)
    (i : Fin (n + 2)) (p : hom (n + 1) X Y) (hp : e = degeneracy (n + 1) i p) :
    desc n value e he = value i p := by
  exact values_agree n value h _ _ _ _ (he.choose_spec.choose_spec.symm.trans hp)

lemma desc_degeneracy (h : Compatible n value) (i : Fin (n + 2)) (p : hom (n + 1) X Y)
    (he : Fixed n (degeneracy (n + 1) i p)) :
    desc n value (degeneracy (n + 1) i p) he = value i p :=
  desc_eq n value h _ he i p rfl

lemma desc_restriction {U : Sort w'} (ρ : T → U) (boundary : hom (n + 2) X Y → U)
    (hρ : ∀ i p, ρ (value i p) = boundary (degeneracy (n + 1) i p))
    (e : hom (n + 2) X Y) (he : Fixed n e) :
    ρ (desc n value e he) = boundary e := by
  rw [desc, hρ, ← he.choose_spec.choose_spec]

/-- 全退化像の和への降下は各退化像上の指定値によって一意に決まる。

宇宙・境界・比較射は各宣言に指定されたものを用いる。
余単位と余乗法、または自由な道の生成射を各次数で明示する。
面・退化の関係式と生成射上の一致から、全体の自然性と比較を導く。
-/
lemma desc_unique (h : Compatible n value)
    (f : (e : hom (n + 2) X Y) → Fixed n e → T)
    (hf : ∀ i p he, f (degeneracy (n + 1) i p) he = value i p)
    (e : hom (n + 2) X Y) (he : Fixed n e) : f e he = desc n value e he := by
  obtain ⟨i, p, rfl⟩ := he
  exact (hf i p _).trans (desc_degeneracy n value h i p _).symm

end SerrePositivity.HomotopyFunctionComplex.FreeGeneratorLatchingValues
