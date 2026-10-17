module

public import Mathlib.AlgebraicTopology.SimplexCategory.GeneratorsRelations.NormalForms

/-!
# 表示された単体圏から通常の単体圏への写像は退化の標準形を区別する

## 概要
表示された単体圏から通常の単体圏への写像は退化の標準形を区別する。
一般に再利用できる道具として分類Aに整理する。

## 方針（定義・証明）
順序写像または面・退化の標準形を明示して単体作用素を計算する。
生成作用素上の一致を、単体恒等式によって全作用素上の一致へ拡張する。

## 規約と注意
圏・対象・射の宇宙と必要な極限の仮定は各宣言に従う。
表示された圏や比較射を、局所化後の同型だけで置き換えない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない（依存監査で確認済み）。
今後はS-構成に現れる圏のnerve、射列、図式間の自然なホモトピーに利用できる。
[棚卸し m0042][inventory]と[計画書 §396][plan]を参照。

[inventory]: ../../../formalization-plans/k-theory-generalization-inventory.md#m0042
[plan]: ../../../formalization-plans/k-theory.md
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Uniqueness of degeneracy normal forms in the presented simplex category

This proves faithfulness on composites of degeneracies, using the adjacent
coincidences of their actual monotone maps. No equivalence of simplex categories
is assumed.
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory SimplexCategoryGenRel

namespace SerrePositivity.SimplexPresentation

lemma admissible_eq_of_eval_eq {m : ℕ} {L K : List ℕ}
    (hL : IsAdmissible m L) (hK : IsAdmissible m K) (hlen : L.length = K.length)
    (heval : ∀ j, j < m + L.length + 1 → simplicialEvalσ L j = simplicialEvalσ K j) :
    L = K := by
  apply hL.sortedLT.eq_of_mem_iff hK.sortedLT
  intro j
  rw [mem_isAdmissible_iff L hL, mem_isAdmissible_iff K hK, ← hlen]
  by_cases hj : j < m + L.length
  · rw [heval j (by omega), heval (j + 1) (by omega)]
  · simp only [hj, false_and]

lemma standardσ_injective {m n : ℕ} {L K : List ℕ}
    (hL : IsAdmissible m L) (hK : IsAdmissible m K)
    (hLn : m + L.length = n) (hKn : m + K.length = n)
    (h : toSimplexCategory.map (standardσ L hLn) =
      toSimplexCategory.map (standardσ K hKn)) : L = K := by
  apply admissible_eq_of_eval_eq hL hK (by omega)
  intro j hj
  have hjn : j < n + 1 := by omega
  have h' := congrArg (fun f : SimplexCategory.mk n ⟶ SimplexCategory.mk m =>
    (f.toOrderHom ⟨j, hjn⟩ : ℕ)) h
  exact (simplicialEvalσ_of_isAdmissible L n m hL hLn j hjn).symm.trans
    (h'.trans (simplicialEvalσ_of_isAdmissible K n m hK hKn j hjn))

/-- 表示された単体圏から通常の単体圏への写像は退化の標準形を区別する。

圏・対象・射の宇宙と必要な極限の仮定は各宣言に従う。
順序写像または面・退化の標準形を明示して単体作用素を計算する。
生成作用素上の一致を、単体恒等式によって全作用素上の一致へ拡張する。
-/
lemma map_injective_on_degeneracies {x y : SimplexCategoryGenRel} {f g : x ⟶ y}
    (hf : P_σ f) (hg : P_σ g) (h : toSimplexCategory.map f = toSimplexCategory.map g) :
    f = g := by
  obtain ⟨L, m, b, rfl, rfl, hlen, hL, rfl⟩ := exists_normal_form_P_σ f hf
  obtain ⟨K, m', b', hy, hx, hlen', hK, hg'⟩ := exists_normal_form_P_σ g hg
  have hm : m' = m := congrArg SimplexCategoryGenRel.len hy
  subst m'
  have hb : b' = b := by
    have := congrArg SimplexCategoryGenRel.len hx
    simp only [mk_len] at this
    omega
  subst b'
  have heq : L = K := standardσ_injective hL hK _ _ (by simpa only [hg'] using h)
  subst K
  exact hg'.symm

end SerrePositivity.SimplexPresentation
