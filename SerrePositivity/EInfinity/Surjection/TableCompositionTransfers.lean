module

public import SerrePositivity.EInfinity.Surjection.TableCompositionBlocks
public import SerrePositivity.EInfinity.TableReduction.FirstReductionState

/-!
# 全成分の共通状態列に対する実際のブロック転送

概要：Berger–Fresse §1.5.7 の水平・垂直・最終ブロックを同じ状態添字へ接続する。
方針：元の出現境界と分割境界の一致を既存の実際の転送定理へ渡す。
規約：元の二つの成功と分割だけを使う。
使われ方：任意の後続成功から全成分列の成功を帰納的に組み立てる。
-/

@[expose] public section

namespace SerrePositivity.EInfinity.Surjection.TableCompositionData

open TableReduction

/-- 概要：第 i 水平成分を共通の状態列で後続へ接続（BF §1.5.7）。
方針：元の二つの成功を既存の水平転送へ渡す。
規約：第 i 出現で終わる成分。
使われ方：全成分列の水平から垂直への接続。 -/
lemma horizontal_transfer {m n d e : ℕ} (c : TableCompositionData m n d e) (i : Fin c.count)
    (rest : List (List (Fin (m + n)) × ℕ)) (tail : List (Fin (m + n)))
    (ht : reduceRows rest (c.betweenState i.val) = some tail) :
    reduceRows (c.horizontalRows i.val ++ rest) (c.state i.val) =
      some (c.horizontalWord i.val ++ tail) := by
  exact componentHorizontalExtraction_success c.outer c.outerSchedule c.outerWord c.outer_success
    c.slot i c.inner c.innerSchedule c.innerWord c.inner_success
    (c.innerPosition i.val) rest tail ht

/-- 概要：第 i 垂直成分を次の水平始状態へ接続（BF §1.5.7）。
方針：分割境界の開始・終了位置の一致で元の垂直転送を同じ状態列へ移す。
規約：次の外側出現位置を固定する。
使われ方：全成分列の垂直から次の水平への接続。 -/
lemma vertical_transfer {m n d e : ℕ} (c : TableCompositionData m n d e) (i : Fin c.count)
    (rest : List (List (Fin (m + n)) × ℕ)) (tail : List (Fin (m + n)))
    (ht : reduceRows rest (c.state (i.val + 1)) = some tail) :
    reduceRows (c.verticalRows i ++ rest) (c.betweenState i.val) =
      some (c.verticalWord i ++ tail) := by
  have hp : c.outerPosition (i.val + 1) = occurrenceAt c.outerWord.val c.slot i := by
    apply Fin.ext
    exact occurrenceBoundary_at c.outerWord.val c.slot i
  have hk : c.outerWord.val (c.outerPosition (i.val + 1)) = c.slot := by
    rw [hp]
    exact occurrenceAt_value c.outerWord.val c.slot i
  have ht' : reduceRows rest (compositionStateRemoved c.slot
      (reductionRemoved c.outer c.outerSchedule c.outerWord.val c.outer_success
        (c.outerPosition (i.val + 1)))
      (reductionRemoved c.inner c.innerSchedule c.innerWord.val c.inner_success
        (c.cuts.endPosition c.inner_positive i))) = some tail := by
    simpa only [state, innerPosition, c.cuts.boundaryPosition_next] using ht
  have hs := componentVerticalExtraction_success c.outer c.outerSchedule c.outerWord
    c.outer_success (c.outerPosition (i.val + 1)) c.slot hk c.inner c.innerSchedule c.innerWord
    c.inner_success c.cuts c.inner_positive i rest tail ht'
  simpa only [verticalRows, verticalWord, betweenState, innerPosition,
    c.cuts.boundaryPosition_at] using hs

/-- 概要：最後の水平成分を共通の始終状態で後続へ接続（BF §1.5.7）。
方針：最後の分割境界が元の内側最終位置であることを既存の最終水平転送へ渡す。
規約：指定値の最終除外を許す。
使われ方：全成分列の末尾を閉じる。 -/
lemma final_transfer {m n d e : ℕ} (c : TableCompositionData m n d e)
    (rest : List (List (Fin (m + n)) × ℕ)) (tail : List (Fin (m + n)))
    (ht : reduceRows rest (c.betweenState c.count) = some tail) :
    reduceRows (c.horizontalRows c.count ++ rest) (c.state c.count) =
      some (c.horizontalWord c.count ++ tail) := by
  exact finalHorizontalExtraction_success c.outer c.outerSchedule c.outerWord c.outer_success
    c.slot c.inner c.innerSchedule c.innerWord c.inner_success (c.innerPosition c.count)
    (c.cuts.boundaryPosition_last c.inner_positive) rest tail ht

/-- 概要：全成分列の最初の合成進行状態は空（BF §1.5.7）。
方針：元の両方の語の最初の位置の進行状態が空であることを使う。
規約：元の外側指定値は全射語のため少なくとも一回現れる。
使われ方：全表の実際の抽出を空の除外状態から始める。 -/
lemma state_zero {m n d e : ℕ} (c : TableCompositionData m n d e) : c.state 0 = [] := by
  have ho : (c.outerPosition 0).val = 0 := occurrenceBoundary_zero c.outerWord.val c.slot
  have hi : (c.innerPosition 0).val = 0 := c.cuts.boundaryPosition_zero c.inner_positive
    (occurrenceCount_pos c.outerWord c.slot)
  unfold state
  rw [reductionRemoved_first_eq_nil c.outer c.outerSchedule c.outerWord.val c.outer_success _ ho,
    reductionRemoved_first_eq_nil c.inner c.innerSchedule c.innerWord.val c.inner_success _ hi]
  simp [compositionStateRemoved, compositionRemoved, remainingLetters]

end SerrePositivity.EInfinity.Surjection.TableCompositionData
