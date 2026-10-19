module

public import SerrePositivity.EInfinity.Surjection.NullaryErasure
public import SerrePositivity.EInfinity.TableReduction.FilterMapAvailable
public import SerrePositivity.EInfinity.TableReduction.FilterMapExcluded

/-!
# nullary 合成行の可用文字

概要：Berger–Fresse §1.5.7 の空語挿入で、除外状態と逆置換行を同時に削除する。
方針：指定値の削除は部分単射なので、既存の filterMap の可用行公式を適用する。
規約：除外リストは重複を持ってもよく、指定値を既に除外していてもよい。
使われ方：空語挿入の table reduction の比較と解放値の逆探索の入口。
-/

@[expose] public section

namespace SerrePositivity.EInfinity.TableReduction

open Surjection

/-- 概要：指定値削除は可用行の計算と可換（BF §1.5.7）。
方針：削除ラベルの部分単射性から available_filterMap を使う。
規約：行・除外状態の長さや非重複性は要求しない。
使われ方：nullary 合成表の状態を元の表へ戻す。 -/
lemma available_eraseSlotWord {m : ℕ} (k : Fin (m + 1))
    (removed row : List (Fin (m + 1))) :
    available (eraseSlotWord k removed) (eraseSlotWord k row) =
      eraseSlotWord k (available removed row) :=
  available_filterMap (eraseSlotLabel k) (eraseSlotLabel_partial_injective k) removed row

/-- 概要：実際の nullary 合成逆行の可用語は元の可用語の指定値削除（BF §1.5.7）。
方針：実際の逆行の削除表示と除外状態の可換公式を連結する。
規約：空集合上の内側置換と任意の元の除外状態。
使われ方：元の表から空語を挿入した表への各抽出ステップの比較。 -/
lemma permutationComposition_nullary_available {m : ℕ}
    (σ : Equiv.Perm (Fin (m + 1))) (τ : Equiv.Perm (Fin 0)) (k : Fin (m + 1))
    (removed : List (Fin (m + 1))) :
    available (eraseSlotWord k removed)
      (List.ofFn (BarrattEccles.permutationComposition m 0 k σ τ).symm) =
      eraseSlotWord k (available removed (List.ofFn σ.symm)) := by
  rw [permutationComposition_inverse_row_nullary, available_eraseSlotWord]

/-- 概要：指定値を既に除外した表の全抽出は削除と可換（BF §1.5.7）。
方針：none となる文字が指定値だけであることを使って一般の部分単射公式を適用する。
規約：元の成功を要求せず、失敗する Schedule も保存する。
使われ方：削除表の成功を、解放値探索に渡す元の早期除外表と照合する。 -/
lemma reduceRows_eraseSlotWord_of_mem {m : ℕ} (k : Fin (m + 1))
    (rows : List (List (Fin (m + 1)) × ℕ)) (removed : List (Fin (m + 1)))
    (hk : k ∈ removed) :
    reduceRows (rows.map (fun p => (eraseSlotWord k p.1, p.2))) (eraseSlotWord k removed) =
      (reduceRows rows removed).map (eraseSlotWord k) := by
  apply reduceRows_filterMap_of_discarded_mem (eraseSlotLabel k)
    (eraseSlotLabel_partial_injective k)
  intro a ha
  by_cases he : a = k
  · exact he ▸ hk
  · simp [eraseSlotLabel, he] at ha

end SerrePositivity.EInfinity.TableReduction
