module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.AWChainMap
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Eilenberg–Zilber の shuffle の格子路

概要：水平ステップの位置の部分集合から二つの単体的退化写像を作る。
方針：各頂点以前の水平ステップ数と垂直ステップ数を数える。
規約：KST Construction A.5 の標準 shuffle。符号は垂直ステップが水平ステップに先行する対の数。
使われ方：正規化全テンソルから次数ごとの単体的テンソルへの実成分写像。

対応節は Kerodon 2.5（Tag 00ND）。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open CategoryTheory
open scoped Simplicial

/-- 概要：n 個のステップのうち p 個を水平にする shuffle の選択。
方針：Fin n の濃度 p の部分集合として表す。
規約：KST A.5、残りの n−p ステップは垂直。
使われ方：標準 shuffle の有限和の添字。 -/
@[kerodon 00RH]
abbrev ShuffleIndex (p n : ℕ) := {s : Finset (Fin n) // s.card = p}

/-- 概要：shuffle の垂直ステップの数は q。
方針：全ステップ n=p+q から水平ステップ p を引く。
規約：KST A.5。使われ方：第二因子への単体写像の値域の上界。 -/
lemma ShuffleIndex.compl_card {p q n : ℕ} (s : ShuffleIndex p n) (h : p + q = n) :
    s.valᶜ.card = q := by
  rw [Finset.card_compl]
  simp only [Fintype.card_fin, s.property]
  omega

/-- 概要：水平ステップ数で定まる shuffle の第一因子への単体写像。
方針：頂点 x より前の水平ステップの数を数える。
規約：KST A.5、反変な単体的加群では退化方向の写像になる。
使われ方：第一因子に適用する標準 shuffle の写像。 -/
@[kerodon 00RH]
def ShuffleIndex.left {p n : ℕ} (s : ShuffleIndex p n) : ⦋n⦌ ⟶ ⦋p⦌ :=
  SimplexCategory.mkHom
    { toFun x := ⟨(s.val.filter (fun j : Fin n ↦ (j : ℕ) < (x : ℕ))).card, by
        have h := Finset.card_filter_le s.val (fun j : Fin n ↦ (j : ℕ) < (x : ℕ))
        rw [s.property] at h
        omega⟩
      monotone' x y hxy := by
        apply Finset.card_le_card
        intro j hj
        rcases Finset.mem_filter.mp hj with ⟨hs, hx⟩
        exact Finset.mem_filter.mpr ⟨hs, lt_of_lt_of_le hx hxy⟩ }

/-- 概要：垂直ステップ数で定まる shuffle の第二因子への単体写像。
方針：頂点 x より前の補集合のステップの数を数える。
規約：KST A.5、全ステップ数 n=p+q。
使われ方：第二因子に適用する標準 shuffle の写像。 -/
@[kerodon 00RH]
def ShuffleIndex.right {p q n : ℕ} (s : ShuffleIndex p n) (h : p + q = n) : ⦋n⦌ ⟶ ⦋q⦌ :=
  SimplexCategory.mkHom
    { toFun x := ⟨(s.valᶜ.filter (fun j : Fin n ↦ (j : ℕ) < (x : ℕ))).card, by
        have h' := Finset.card_filter_le s.valᶜ (fun j : Fin n ↦ (j : ℕ) < (x : ℕ))
        rw [s.compl_card h] at h'
        omega⟩
      monotone' x y hxy := by
        apply Finset.card_le_card
        intro j hj
        rcases Finset.mem_filter.mp hj with ⟨hs, hx⟩
        exact Finset.mem_filter.mpr ⟨hs, lt_of_lt_of_le hx hxy⟩ }

/-- 概要：shuffle の交代符号を定める逆転の数。
方針：各水平ステップに先行する垂直ステップの数を足す。
規約：KST A.5 の標準 shuffle の符号 (−1)^inv。
使われ方：実 shuffle の成分の有限和。 -/
@[kerodon 00RH]
def ShuffleIndex.inversions {p n : ℕ} (s : ShuffleIndex p n) : ℕ :=
  ∑ j ∈ s.val, (s.valᶜ.filter (fun k ↦ k < j)).card

/-- 概要：shuffle の第一写像は水平ステップ数を値とする。
方針：順序写像の定義を評価する。
規約：KST A.5。使われ方：面と退化の格子路の計算。 -/
@[simp] lemma ShuffleIndex.left_apply {p n : ℕ} (s : ShuffleIndex p n) (x : Fin (n + 1)) :
    (s.left.toOrderHom x : ℕ) = (s.val.filter (fun j : Fin n ↦ (j : ℕ) < (x : ℕ))).card := rfl

/-- 概要：shuffle の第二写像は垂直ステップ数を値とする。
方針：順序写像の定義を評価する。
規約：KST A.5。使われ方：面と退化の格子路の計算。 -/
@[simp] lemma ShuffleIndex.right_apply {p q n : ℕ} (s : ShuffleIndex p n)
    (h : p + q = n) (x : Fin (n + 1)) :
    ((s.right h).toOrderHom x : ℕ) = (s.valᶜ.filter (fun j : Fin n ↦ (j : ℕ) < (x : ℕ))).card := rfl

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
