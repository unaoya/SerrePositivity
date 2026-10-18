module

public import SerrePositivity.EInfinity.BarrattEccles.PermutationCompositionValues

/-!
# 異なる二入力への挿入の数値的な位置の比較

概要：Berger–Fresse §0.10 の独立な二入力への代入順序による位置の変化を比較する。
方針：残りの入力の番号の分岐を展開し、指定位置の前後で加減算を比較する。
規約：二つの指定位置は異なり、挿入する arity は0を含んでよい。
使われ方：置換の部分合成の並列結合則の位置の補題となる。
-/

@[expose] public section

namespace SerrePositivity.EInfinity.BarrattEccles

/-- 概要：異なる二入力への挿入で残りの入力の最終番号は順序に依存しない（Berger–Fresse §0.10）。
方針：元の番号が指定した二入力の前・間・後にある場合を加減算へ直す。
規約：a は指定位置 i,j の両方と異なる。
使われ方：並列結合則の外側の残りの入力を比較する。 -/
lemma remainingValue_parallel (n k i j a : ℕ) (hij : i ≠ j) (hai : a ≠ i) (haj : a ≠ j) :
    remainingValue k (remainingValue n i j) (remainingValue n i a) =
      remainingValue n (remainingValue k j i) (remainingValue k j a) := by
  simp only [remainingValue]
  split_ifs <;> omega

/-- 概要：一方の挿入区間の入力は他方の挿入による位置移動だけを受ける（Berger–Fresse §0.10）。
方針：二つの指定位置の順序で分け、区間の長さの上界を使って番号を計算する。
規約：a は長さ n の最初の挿入区間の内側の番号である。
使われ方：並列結合則の二つの内側の入力を比較する。 -/
lemma insertedValue_parallel (n k i j a : ℕ) (hij : i ≠ j) (ha : a < n) :
    remainingValue k (remainingValue n i j) (i + a) = remainingValue k j i + a := by
  simp only [remainingValue]
  split_ifs <;> omega

/-- 概要：挿入後の残りの入力の番号は元の番号を一意に定める（Berger–Fresse §0.10）。
方針：二つの元の入力が挿入位置より前か後かで分け、値の等式を解く。
規約：二つの入力とも挿入位置そのものではない。
使われ方：二回目の指定位置と異なることから元の二入力の相違を復元する。 -/
lemma remainingValue_injective (n i a b : ℕ) (ha : a ≠ i) (hb : b ≠ i)
    (h : remainingValue n i a = remainingValue n i b) : a = b := by
  simp only [remainingValue] at h
  split_ifs at h <;> omega

/-- 概要：残りの入力の番号は挿入区間のどの番号とも異なる（Berger–Fresse §0.10）。
方針：元の入力の位置の前後と挿入区間の上界を用いる。
規約：a は元の残りの入力、b は新しい区間の入力である。
使われ方：並列の二回目の挿入で一方の挿入区間が残ることを保証する。 -/
lemma remainingValue_ne_inserted (n i a b : ℕ) (ha : a ≠ i) (hb : b < n) :
    remainingValue n i a ≠ i + b := by
  simp only [remainingValue]
  split_ifs <;> omega

end SerrePositivity.EInfinity.BarrattEccles
