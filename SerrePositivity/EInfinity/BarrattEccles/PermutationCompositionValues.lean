module

public import SerrePositivity.EInfinity.BarrattEccles.PermutationComposition

/-!
# 置換の部分合成の入力位置での値

概要：Berger–Fresse §0.10 の置換の部分合成を挿入区間の内側と残りの入力で計算する。
方針：挿入分解の逆同値を位置の表示として使い、値の計算を自然数の挿入に帰着する。
規約：arity 0 の挿入も含み、残りの入力は挿入位置と異なると仮定する。
使われ方：置換の部分合成の入れ子・並列の結合則を入力ごとに証明する。
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.EInfinity.BarrattEccles

/-- 概要：一つの位置を n 個へ置換したときの残りの入力の番号（Berger–Fresse §0.10）。
方針：指定位置より前は固定し、後ろは n−1 だけずらす。
規約：等式の右側では自然数の切り詰めた減算を使う。
使われ方：二段の挿入の位置の等式を数値で計算する。 -/
def remainingValue (n i a : ℕ) : ℕ := if a < i then a else a + n - 1

/-- 概要：挿入後にも残る外側の入力の位置（Berger–Fresse §0.10）。
方針：挿入分解の逆同値を左成分で評価する。
規約：元の入力は指定位置 i と異なる。
使われ方：部分合成の残りの入力への作用を記述する。 -/
def remainingPosition (m n : ℕ) (i : Fin (m + 1))
    (a : {a : Fin (m + 1) // a ≠ i}) : Fin (m + n) :=
  (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadInsertionEquiv m n i).symm (Sum.inl a)

/-- 概要：挿入区間の内側の入力の位置（Berger–Fresse §0.10）。
方針：挿入分解の逆同値を右成分で評価する。
規約：内側の位置 a の出力番号は i+a である。
使われ方：部分合成の内側の入力への作用を記述する。 -/
def insertedPosition (m n : ℕ) (i : Fin (m + 1)) (a : Fin n) : Fin (m + n) :=
  (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadInsertionEquiv m n i).symm (Sum.inr a)

/-- 概要：残りの入力の位置の値は自然数の挿入公式に一致する（Berger–Fresse §0.10）。
方針：挿入分解の逆写像の定義を計算する。
規約：残りの入力が挿入位置より前かどうかで分岐する。
使われ方：結合則で位置の型の違いを値の等式へ帰着する。 -/
lemma remainingPosition_val (m n : ℕ) (i : Fin (m + 1))
    (a : {a : Fin (m + 1) // a ≠ i}) :
    (remainingPosition m n i a).val = remainingValue n i.val a.val.val := by
  simp only [remainingPosition, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadInsertionEquiv, Equiv.coe_fn_symm_mk, remainingValue]
  split_ifs <;> rfl

/-- 概要：挿入区間の位置の値は二つの入力番号の和である（Berger–Fresse §0.10）。
方針：挿入分解の逆写像の右成分を計算する。
規約：外側の指定位置と内側の位置はともに0始まりである。
使われ方：入れ子の最内層の入力を追跡する。 -/
lemma insertedPosition_val (m n : ℕ) (i : Fin (m + 1)) (a : Fin n) :
    (insertedPosition m n i a).val = i.val + a.val := rfl

/-- 概要：残りの入力と挿入区間の入力は異なる（Berger–Fresse §0.10）。
方針：挿入分解の逆同値の単射性を左右の直和成分へ適用する。
規約：内側 arity が0なら主張の入力は存在しない。
使われ方：二段目の挿入で元の外側の入力が残ることを示す。 -/
lemma remainingPosition_ne_inserted (m n : ℕ) (i : Fin (m + 1))
    (a : {a : Fin (m + 1) // a ≠ i}) (b : Fin n) :
    remainingPosition m n i a ≠ insertedPosition m n i b := by
  intro h
  cases (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadInsertionEquiv m n i).symm.injective h

/-- 概要：置換の部分合成は残りの入力を外側の置換で動かす（Berger–Fresse §0.10）。
方針：内側の置換が残りの入力を固定することと外側置換の値の公式を使う。
規約：出力側の挿入位置は σ(i) である。
使われ方：結合則の外側と中間の残りの入力の計算に用いる。 -/
lemma permutationComposition_remaining (m n : ℕ) (i : Fin (m + 1))
    (σ : Equiv.Perm (Fin (m + 1))) (τ : Equiv.Perm (Fin n))
    (a : {a : Fin (m + 1) // a ≠ i}) :
    permutationComposition m n i σ τ (remainingPosition m n i a) =
      remainingPosition m n (σ i) ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadRemainingEquiv m i σ) a) := by
  have hinner : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadInnerPermutation m n i τ (remainingPosition m n i a) =
      remainingPosition m n i a := by
    simp only [remainingPosition, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadInnerPermutation, Equiv.trans_apply,
      Equiv.apply_symm_apply, Equiv.sumCongr_apply, Sum.map_inl, Equiv.refl_apply]
  rw [permutationComposition, Equiv.Perm.mul_apply, hinner]
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadOuterPermutation_remaining m n i σ a

/-- 概要：置換の部分合成は挿入区間の入力を内側の置換で動かす（Berger–Fresse §0.10）。
方針：内側置換の区間内の値と外側置換の区間移動の公式を続けて使う。
規約：入力 i+a は出力 σ(i)+τ(a) へ移る。
使われ方：入れ子の最内層の入力を比較する。 -/
lemma permutationComposition_inside (m n : ℕ) (i : Fin (m + 1))
    (σ : Equiv.Perm (Fin (m + 1))) (τ : Equiv.Perm (Fin n)) (a : Fin n) :
    permutationComposition m n i σ τ (insertedPosition m n i a) =
      insertedPosition m n (σ i) (τ a) := by
  change permutationComposition m n i σ τ ⟨i.val + a.val, by omega⟩ =
    ⟨(σ i).val + (τ a).val, by have h := (σ i).isLt; have h' := (τ a).isLt; omega⟩
  rw [permutationComposition, Equiv.Perm.mul_apply, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadInnerPermutation_inside,
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadOuterPermutation_inside]

/-- 概要：残りの入力に対する部分合成の値を自然数で表す（Berger–Fresse §0.10）。
方針：残りの入力の作用の公式に位置の値の公式を適用する。
規約：出力番号は外側置換の像とその指定位置から決まる。
使われ方：結合則の残りの入力の比較を自然数の等式に直す。 -/
lemma permutationComposition_remaining_val (m n : ℕ) (i : Fin (m + 1))
    (σ : Equiv.Perm (Fin (m + 1))) (τ : Equiv.Perm (Fin n))
    (a : {a : Fin (m + 1) // a ≠ i}) :
    (permutationComposition m n i σ τ (remainingPosition m n i a)).val =
      remainingValue n (σ i).val (σ a.val).val := by
  rw [permutationComposition_remaining, remainingPosition_val]
  rfl

/-- 概要：入れ子の挿入後も外側の残りの入力の番号は合成した arity だけで決まる（Berger–Fresse §0.10）。
方針：元の入力が指定位置より前か後かで分け、二回のずれを加減算する。
規約：内側の指定位置 j は n 以下、外側の残りの入力 a は i と異なる。
使われ方：入れ子の結合則の外側の入力を比較する。 -/
lemma remainingValue_nested_outer (n k i j a : ℕ) (hj : j ≤ n) (_ha : a ≠ i) :
    remainingValue k (i + j) (remainingValue (n + 1) i a) = remainingValue (n + k) i a := by
  by_cases hlt : a < i
  · have hc : a < i + j := by omega
    simp only [remainingValue, ite_eq_left hlt, ite_eq_left hc]
  · have hc : ¬a + (n + 1) - 1 < i + j := by omega
    simp only [remainingValue, ite_eq_right hlt, ite_eq_right hc]
    omega

/-- 概要：入れ子の内側の残りの入力の番号は外側の指定位置で平行移動する（Berger–Fresse §0.10）。
方針：内側の入力が内側の指定位置より前か後かで分け、加法と減算を整理する。
規約：内側の残りの入力 a は指定位置 j と異なる。
使われ方：入れ子の結合則の中間の入力を比較する。 -/
lemma remainingValue_nested_inner (k i j a : ℕ) (ha : a ≠ j) :
    remainingValue k (i + j) (i + a) = i + remainingValue k j a := by
  by_cases hlt : a < j
  · have hc : i + a < i + j := by omega
    simp only [remainingValue, ite_eq_left hlt, ite_eq_left hc]
  · have hc : ¬i + a < i + j := by omega
    simp only [remainingValue, ite_eq_right hlt, ite_eq_right hc]
    omega

end SerrePositivity.EInfinity.BarrattEccles
