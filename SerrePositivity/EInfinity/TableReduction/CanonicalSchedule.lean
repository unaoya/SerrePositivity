module

public import SerrePositivity.EInfinity.TableReduction.CanonicalExtraction
public import SerrePositivity.EInfinity.TableReduction.CanonicalLastRow

/-!
# 全射語の標準行長の Schedule

概要：Berger–Fresse §1.4.3 の正しい行長を既存の有限な Schedule の元へ束ねる。
方針：区切りまでの長さと最後の残りの長さを定め、望遠和で総和を計算する。
規約：正の arity で各行長は正であり n 以下。
使われ方：TR の和の唯一の非退化項の添字を指定する。
-/

@[expose] public section

namespace SerrePositivity.EInfinity.TableReduction

open Surjection

/-- 概要：全射語の標準 table の各行の長さ（BF §1.4.3）。
方針：最後以外は cut−start+1、最後は語の残りの長さ。
規約：長さは自然数。
使われ方：正しい抽出の行長を全行で同時に指定する。 -/
def canonicalLengths {n d : ℕ} (v : BasisWord n d) : Fin (d + 1) → ℕ :=
  Fin.lastCases (n + d - rowStart v (Fin.last d))
    (fun i => (caesuraAt v i).val - rowStart v i.castSucc + 1)

/-- 概要：最後以外の標準行長の式（BF §1.4.3）。
方針：lastCases の前半の分岐を評価する。
規約：i は Fin d。
使われ方：各行の抽出と行長の強制を適用する。 -/
@[simp] lemma canonicalLengths_castSucc {n d : ℕ} (v : BasisWord n d) (i : Fin d) :
    canonicalLengths v i.castSucc = (caesuraAt v i).val - rowStart v i.castSucc + 1 :=
  Fin.lastCases_castSucc i

/-- 概要：最後の標準行長の式（BF §1.4.3）。
方針：lastCases の最後の分岐を評価する。
規約：開始位置から終端までの長さ。
使われ方：最後の行の抽出の基底となる。 -/
@[simp] lemma canonicalLengths_last {n d : ℕ} (v : BasisWord n d) :
    canonicalLengths v (Fin.last d) = n + d - rowStart v (Fin.last d) :=
  Fin.lastCases_last

/-- 概要：行長を加えると次の行の開始位置になる（BF §1.4.3）。
方針：開始位置は区切り以下で、次の開始位置は区切りの直後。
規約：最後の行を除く。
使われ方：行長の総和と抽出した語の連結を計算する。 -/
lemma canonicalLengths_add_start {n d : ℕ} (v : BasisWord n d) (i : Fin d) :
    canonicalLengths v i.castSucc + rowStart v i.castSucc = rowStart v i.succ := by
  rw [canonicalLengths_castSucc, rowStart_succ_eq_caesuraAt]
  have hs := rowStart_le_caesuraAt v i
  omega

/-- 概要：全ての標準行長の総和は語の長さ（BF §1.4.3）。
方針：各行の開始位置を足した等式を加算し、共通の和を消去する。
規約：空語も含めて成立する。
使われ方：標準行長を Schedule の総和条件へ束ねる。 -/
lemma canonicalLengths_sum {n d : ℕ} (v : BasisWord n d) :
    (∑ i, canonicalLengths v i) = n + d := by
  have hs : (∑ i : Fin d, canonicalLengths v i.castSucc) +
      (∑ i : Fin d, rowStart v i.castSucc) = ∑ i : Fin d, rowStart v i.succ := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    exact canonicalLengths_add_start v i
  have hcast := Fin.sum_univ_castSucc (rowStart v)
  have hsucc := Fin.sum_univ_succ (rowStart v)
  rw [rowStart_zero] at hsucc
  have hb := rowStart_le_length v (Fin.last d)
  rw [Fin.sum_univ_castSucc, canonicalLengths_last]
  omega

/-- 概要：正の arity の標準行長は全て正（BF §1.4.3）。
方針：通常行には 1 が加わり、最後の開始位置は終端より前にある。
規約：nullary 空語の分岐は含めない。
使われ方：Schedule の正値条件を供給する。 -/
lemma canonicalLengths_pos {n d : ℕ} (v : BasisWord n d) (hn : 0 < n)
    (i : Fin (d + 1)) : 0 < canonicalLengths v i := by
  cases i using Fin.lastCases with
  | last =>
    rw [canonicalLengths_last]
    have hs := rowStart_lt_length v hn (Fin.last d)
    omega
  | cast i => rw [canonicalLengths_castSucc]; omega

/-- 概要：標準行長は除外後の行の長さ以下（BF §1.4.3）。
方針：指定した抽出の長さを take する元の行の長さで評価する。
規約：最後の行では残りの長さに等しい。
使われ方：正しい行長で reduceRows の分岐が成功することを示す。 -/
lemma canonicalLengths_le_available {n d : ℕ} (v : BasisWord n d) (i : Fin (d + 1)) :
    canonicalLengths v i ≤
      (available (pastFinals (List.ofFn v.val) (rowStart v i))
        (canonicalRow (List.ofFn v.val) (rowStart v i))).length := by
  cases i using Fin.lastCases with
  | last =>
    simp only [canonicalLengths_last, available_canonicalRow_last,
      List.length_drop, List.length_ofFn, Nat.le_refl]
  | cast i =>
    have ht : ((available (pastFinals (List.ofFn v.val) (rowStart v i.castSucc))
        (canonicalRow (List.ofFn v.val) (rowStart v i.castSucc))).take
          ((finalSegment v i).length + 1)).length ≤
        (available (pastFinals (List.ofFn v.val) (rowStart v i.castSucc))
          (canonicalRow (List.ofFn v.val) (rowStart v i.castSucc))).length := by
      rw [List.length_take]
      exact Nat.min_le_right _ _
    rw [canonicalRows_selected_prefix, List.length_append, List.length_singleton,
      finalSegment_length] at ht
    simpa only [canonicalLengths_castSucc] using ht

/-- 概要：標準行長は arity 以下（BF §1.4.3）。
方針：除外後の行の長さと元の置換の長さで評価する。
規約：行長が正であることとは独立の不等式。
使われ方：行長を Fin(n+1) の有限添字へ入れる。 -/
lemma canonicalLengths_le_arity {n d : ℕ} (v : BasisWord n d) (i : Fin (d + 1)) :
    canonicalLengths v i ≤ n := by
  have hf := List.length_filter_le
    (fun x => decide (x ∉ pastFinals (List.ofFn v.val) (rowStart v i)))
    (canonicalRow (List.ofFn v.val) (rowStart v i))
  rw [canonicalRow_word_length] at hf
  exact Nat.le_trans (canonicalLengths_le_available v i) hf

/-- 概要：全射語が指定する唯一の非退化項の行長の候補（BF §1.4.3）。
方針：各行長を有限添字に入れ、正値性と総和を束ねる。
規約：正の arity で定義する。
使われ方：一般の TR の和をこの一項に帰着する。 -/
def canonicalSchedule {n d : ℕ} (v : BasisWord n d) (hn : 0 < n) : Schedule n d :=
  ⟨fun i => ⟨canonicalLengths v i, Nat.lt_succ_of_le (canonicalLengths_le_arity v i)⟩,
    canonicalLengths_pos v hn, canonicalLengths_sum v⟩

end SerrePositivity.EInfinity.TableReduction
