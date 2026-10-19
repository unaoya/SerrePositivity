module

public import SerrePositivity.EInfinity.TableReduction.CanonicalFilteredRows
public import SerrePositivity.EInfinity.Surjection.FinalSuffix

/-!
# 標準 table の最後の行の抽出

概要：Berger–Fresse §1.4.3 の最後の行は元の語の残り全体を返す。
方針：最後の尾部は重複しないため最初の出現の選択が恒等になる。
規約：正の arity で抽出の正の長さを証明し、nullary 分岐とは別に扱う。
使われ方：全行の抽出の帰納法の最終段階となる。
-/

@[expose] public section

namespace SerrePositivity.EInfinity.TableReduction

open Surjection

/-- 概要：最後の標準行の除外後には元の語の尾部全体が残る（BF §1.4.3）。
方針：確定済みの先頭を除き、重複のない尾部の最初の出現を簡約する。
規約：零 arity の空語も含む等式。
使われ方：最後の行の正しい長さと抽出値を計算する。 -/
lemma available_canonicalRow_last {n d : ℕ} (v : BasisWord n d) :
    available (pastFinals (List.ofFn v.val) (rowStart v (Fin.last d)))
      (canonicalRow (List.ofFn v.val) (rowStart v (Fin.last d))) =
        (List.ofFn v.val).drop (rowStart v (Fin.last d)) := by
  have hn := canonicalRow_nodup (List.ofFn v.val) (rowStart v (Fin.last d))
  unfold canonicalRow at hn ⊢
  rw [available_prefix_of_nodup _ _ hn, firstOccurrences_eq_self _ (last_suffix_nodup v)]

/-- 概要：最後の正しい行長で抽出すると残りの語を得る（BF §1.4.3）。
方針：残りの行の長さ全体を take する。
規約：正の arity を仮定し、行長が正であることを供給する。
使われ方：標準逆像の全行の reduceRows の帰納法の基底となる。 -/
lemma reduceRows_canonical_last {n d : ℕ} (v : BasisWord n d) (hn : 0 < n) :
    reduceRows
      [(canonicalRow (List.ofFn v.val) (rowStart v (Fin.last d)),
        n + d - rowStart v (Fin.last d))]
      (pastFinals (List.ofFn v.val) (rowStart v (Fin.last d))) =
        some ((List.ofFn v.val).drop (rowStart v (Fin.last d))) := by
  have hlen : ((List.ofFn v.val).drop (rowStart v (Fin.last d))).length =
      n + d - rowStart v (Fin.last d) := by simp only [List.length_drop, List.length_ofFn]
  have hpos : 0 < ((List.ofFn v.val).drop (rowStart v (Fin.last d))).length := by
    rw [hlen]
    have hs := rowStart_lt_length v hn (Fin.last d)
    omega
  rw [← hlen]
  simp only [reduceRows, available_canonicalRow_last, hpos, Nat.le_refl,
    and_self, ↓reduceIte, List.take_length, Option.map_some, List.append_nil]

end SerrePositivity.EInfinity.TableReduction
